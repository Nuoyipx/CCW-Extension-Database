'use strict';

const fs = require('fs');
const path = require('path');
const os = require('os');
const cp = require('child_process');
const parser = require('@babel/parser');

const DATABASE_FILE = 'blocks_database.json';
const REPORT_FILE = 'extraction_report.json';
const VERSION_FILE = 'version_report.json';
const DIFF_FILE = 'extraction_diff.json';
const MISSING_FILE = 'unresolved_blocks.json';
const QUALITY_FILE = 'quality_report.json';
const USABLE_FILE = 'usable_blocks.json';
const DIAGNOSTICS_FILE = 'translation_diagnostics.json';
const MAX_IMPORT_DEPTH = 4;
const MAX_LOCALE_FILES = 40;
const MINIMUM_QUALITY = Number(process.env.MINIMUM_QUALITY || 0);

const EXCLUDED_DIRS = new Set(['.git', 'node_modules', '__pycache__', 'dist', 'build', 'assets', 'coverage']);
const EXCLUDED_FILES = new Set(['webpack.config.js', 'vite.config.js', '.eslintrc.js', 'babel.config.js', 'jest.config.js']);
const UNRESOLVED = (source) => ({ $expression: source || '<unknown>' });

function now() { return new Date().toISOString(); }
function sourceOf(node) {
  if (!node) return '';
  if (node.type === 'Identifier') return node.name;
  if (node.type === 'StringLiteral') return JSON.stringify(node.value);
  if (node.type === 'NumericLiteral') return String(node.value);
  if (node.type === 'MemberExpression') return `${sourceOf(node.object)}.${node.computed ? `[${sourceOf(node.property)}]` : sourceOf(node.property)}`;
  if (node.type === 'CallExpression') return `${sourceOf(node.callee)}(...)`;
  if (node.type === 'TemplateLiteral') return '`' + node.quasis.map(q => q.value.cooked || '').join('${...}') + '`';
  return node.type || '<expression>';
}
function keyOf(node, env) {
  if (!node) return null;
  if (node.type === 'Identifier') return node.name;
  if (node.type === 'StringLiteral' || node.type === 'NumericLiteral') return String(node.value);
  if (node.type === 'TemplateLiteral' && node.expressions.length === 0) return node.quasis[0].value.cooked;
  const value = evaluate(node, env, 0);
  return typeof value === 'string' || typeof value === 'number' ? String(value) : null;
}
function unresolved(node) { return UNRESOLVED(sourceOf(node)); }
function isUnresolved(value) {
  if (Array.isArray(value)) return value.some(isUnresolved);
  if (value && typeof value === 'object') return Object.prototype.hasOwnProperty.call(value, '$expression') || Object.values(value).some(isUnresolved);
  return false;
}
function messageLookup(key, env) {
  if (typeof key !== 'string') return null;
  if (Object.prototype.hasOwnProperty.call(env.messages, key)) return env.messages[key];
  return null;
}
function resolveTranslationArg(arg, env) {
  if (typeof arg === 'string') return messageLookup(arg, env) ?? arg;
  if (arg && typeof arg === 'object' && !isUnresolved(arg)) {
    const key = arg.id ?? arg.key ?? arg.messageId;
    const translated = messageLookup(key, env);
    if (typeof translated === 'string') return translated;
    const fallback = arg.defaultMessage ?? arg.default ?? arg.message ?? arg.text;
    if (typeof fallback === 'string') return fallback;
  }
  return null;
}
function evaluate(node, env, depth = 0) {
  if (!node || depth > 24) return unresolved(node);
  const next = (n) => evaluate(n, env, depth + 1);
  switch (node.type) {
    case 'StringLiteral': case 'NumericLiteral': case 'BooleanLiteral': return node.value;
    case 'NullLiteral': return null;
    case 'BigIntLiteral': return node.value;
    case 'Identifier':
      if (node.name === 'undefined') return null;
      if (node.name === 'NaN') return NaN;
      if (Object.prototype.hasOwnProperty.call(env.symbols, node.name)) return env.symbols[node.name];
      if (['EVENT', 'COMMAND', 'REPORTER', 'BOOLEAN', 'HAT', 'CONDITIONAL', 'LOOP', 'STRING', 'NUMBER', 'ANGLE', 'COLOR', 'MATRIX', 'IMAGE'].includes(node.name)) return node.name;
      return unresolved(node);
    case 'ArrayExpression': {
      const values = [];
      for (const el of node.elements) {
        if (!el) { values.push(null); continue; }
        if (el.type === 'SpreadElement') {
          const spread = next(el.argument);
          if (Array.isArray(spread)) values.push(...spread);
          else values.push({ $spread: spread });
        } else values.push(next(el));
      }
      return values;
    }
    case 'ObjectExpression': {
      const out = {};
      for (const prop of node.properties) {
        if (prop.type === 'SpreadElement') { const spread = next(prop.argument); if (spread && typeof spread === 'object' && !Array.isArray(spread) && !isUnresolved(spread)) Object.assign(out, spread); else out.$spread = spread; continue; }
        if (prop.type !== 'ObjectProperty') continue;
        const key = prop.computed ? keyOf(prop.key, env) : (prop.key.name ?? prop.key.value);
        if (key === null) { out.$computed = unresolved(prop.key); continue; }
        out[String(key)] = next(prop.value);
      }
      return out;
    }
    case 'TemplateLiteral': {
      let out = '';
      for (let i = 0; i < node.quasis.length; i++) {
        out += node.quasis[i].value.cooked ?? node.quasis[i].value.raw;
        if (i < node.expressions.length) {
          const value = next(node.expressions[i]);
          if (isUnresolved(value) || value === null || value === undefined) return unresolved(node);
          out += String(value);
        }
      }
      return out;
    }
    case 'MemberExpression': {
      const objectName = node.object.type === 'Identifier' ? node.object.name : null;
      const property = node.computed ? keyOf(node.property, env) : node.property.name;
      if (objectName && ['BlockType', 'ArgumentType', 'TargetType', 'MenuType', 'Cast'].includes(objectName) && property) return property;
      if (node.object.type === 'MemberExpression' && ['Scratch.BlockType', 'Scratch.ArgumentType', 'Scratch.TargetType'].includes(sourceOf(node.object)) && property) return property;
      const base = next(node.object);
      if (base && typeof base === 'object' && property !== null && property in base) return base[property];
      return unresolved(node);
    }
    case 'CallExpression': {
      const callee = node.callee;
      const isFormat = callee.type === 'MemberExpression' && callee.property.name === 'formatMessage';
      if (isFormat && node.arguments.length) {
        const first = next(node.arguments[0]);
        if (typeof first === 'string') return env.messages[first] ?? first;
        if (first && typeof first === 'object' && !isUnresolved(first)) {
          const id = first.id || first.key;
          const fallback = first.defaultMessage ?? first.default ?? first.message;
          if (id && Object.prototype.hasOwnProperty.call(env.messages, id)) return env.messages[id];
          if (typeof fallback === 'string') return fallback;
        }
      }
      // Many CCW extensions use this.fm('key') or this.formatMessage('key').
      // Only resolve keys found in statically collected locale dictionaries;
      // never assume an unknown translation key is user-facing block text.
      if (callee.type === 'MemberExpression' &&
          ['fm', 'formatMessage', 'translate', 't'].includes(callee.property.name) &&
          node.arguments.length) {
        const arg = next(node.arguments[0]);
        const translated = resolveTranslationArg(arg, env);
        if (typeof translated === 'string' &&
            (callee.property.name !== 'fm' || messageLookup(arg, env) !== null ||
             (arg && typeof arg === 'object' && !isUnresolved(arg)))) return translated;
      }
      const name = sourceOf(callee);
      if (['Scratch.translate', 'translate', 'formatMessage', 'Scratch.translate.formatMessage'].includes(name) && node.arguments.length) {
        const arg = next(node.arguments[0]);
        if (typeof arg === 'string') return env.messages[arg] ?? arg;
        if (arg && typeof arg === 'object') {
          const fallback = arg.defaultMessage ?? arg.default ?? arg.message;
          if (arg.id && typeof env.messages[arg.id] === 'string') return env.messages[arg.id];
          if (typeof fallback === 'string') return fallback;
        }
      }
      if (callee.type === 'MemberExpression' && callee.property.name === 'concat') {
        const base = next(callee.object);
        if (Array.isArray(base)) {
          const rest = node.arguments.map(next);
          return base.concat(...rest);
        }
      }
      if (callee.type === 'MemberExpression' && callee.property.name === 'map') {
        const base = next(callee.object);
        const fn = node.arguments[0];
        if (Array.isArray(base) && fn && (fn.type === 'ArrowFunctionExpression' || fn.type === 'FunctionExpression') && fn.params.length && fn.params[0].type === 'Identifier' && base.length <= 1000) {
          const mapped = base.map((item, index) => {
            const scoped = { ...env, symbols: { ...env.symbols, [fn.params[0].name]: item } };
            if (fn.params[1] && fn.params[1].type === 'Identifier') scoped.symbols[fn.params[1].name] = index;
            const body = fn.body.type === 'BlockStatement' ? fn.body.body.find(x => x.type === 'ReturnStatement')?.argument : fn.body;
            return body ? evaluate(body, scoped, depth + 1) : unresolved(fn);
          });
          return mapped;
        }
      }
      if (callee.type === 'MemberExpression' && ['join', 'at'].includes(callee.property.name)) {
        const base = next(callee.object);
        const args = node.arguments.map(next);
        if (Array.isArray(base) && args.every(a => !isUnresolved(a))) {
          if (callee.property.name === 'join') return base.join(args.length ? String(args[0]) : ',');
          if (callee.property.name === 'at') return base.at(Number(args[0]));
        }
      }
      if (name === 'Array.of') return node.arguments.map(next);
      if (name === 'Array.from' && node.arguments.length) {
        const input = next(node.arguments[0]);
        if (Array.isArray(input) && input.length <= 1000) return input;
      }
      if (callee.type === 'MemberExpression' && ['filter', 'slice'].includes(callee.property.name)) {
        const base = next(callee.object);
        if (Array.isArray(base) && callee.property.name === 'slice' && node.arguments.every(a => !isUnresolved(next(a)))) return base.slice(...node.arguments.map(next));
      }
      return unresolved(node);
    }
    case 'UnaryExpression': {
      const value = next(node.argument);
      if (isUnresolved(value)) return unresolved(node);
      if (node.operator === '-') return -Number(value);
      if (node.operator === '+') return Number(value);
      if (node.operator === '!') return !value;
      if (node.operator === '~') return ~Number(value);
      return unresolved(node);
    }
    case 'BinaryExpression': {
      const left = next(node.left), right = next(node.right);
      if (isUnresolved(left) || isUnresolved(right)) return unresolved(node);
      if (node.operator === '+') return typeof left === 'string' || typeof right === 'string' ? String(left) + String(right) : Number(left) + Number(right);
      if (node.operator === '-') return Number(left) - Number(right);
      if (node.operator === '*') return Number(left) * Number(right);
      if (node.operator === '/') return Number(left) / Number(right);
      return unresolved(node);
    }
    case 'ConditionalExpression': {
      const test = next(node.test);
      if (isUnresolved(test)) return unresolved(node);
      return next(test ? node.consequent : node.alternate);
    }
    case 'LogicalExpression': {
      const left = next(node.left);
      if (isUnresolved(left)) return unresolved(node);
      if (node.operator === '||') return left ? left : next(node.right);
      if (node.operator === '&&') return left ? next(node.right) : left;
      if (node.operator === '??') return left === null || left === undefined ? next(node.right) : left;
      return unresolved(node);
    }
    case 'ObjectProperty': return next(node.value);
    case 'SequenceExpression': return node.expressions.length ? next(node.expressions[node.expressions.length - 1]) : null;
    case 'ArrayPattern': return unresolved(node);
    case 'ObjectPattern': return unresolved(node);
    case 'ParenthesizedExpression':
    case 'TSAsExpression': case 'TypeCastExpression': return next(node.expression);
    default: return unresolved(node);
  }
}
function walk(node, callback) {
  if (!node || typeof node !== 'object') return;
  if (typeof node.type === 'string') callback(node);
  for (const [key, value] of Object.entries(node)) {
    if (key === 'loc' || key === 'start' || key === 'end' || key === 'leadingComments' || key === 'trailingComments' || key === 'innerComments') continue;
    if (Array.isArray(value)) value.forEach(v => walk(v, callback));
    else if (value && typeof value === 'object') walk(value, callback);
  }
}
function buildSymbols(ast) {
  const symbols = {};
  const declarations = [];
  walk(ast, node => {
    if (node.type === 'VariableDeclarator' && node.id.type === 'Identifier' && node.init)
      declarations.push([node.id.name, node.init]);
  });
  // Resolve forward references in several passes, without executing extension code.
  for (let pass = 0; pass < 8; pass++) {
    let changed = false;
    for (const [name, init] of declarations) {
      if (Object.prototype.hasOwnProperty.call(symbols, name)) continue;
      const value = evaluate(init, { symbols, messages: {} });
      if (!isUnresolved(value)) { symbols[name] = value; changed = true; }
    }
    if (!changed) break;
  }
  return symbols;
}
function extractMessages(ast) {
  const tables = { 'zh-cn': {}, en: {} };
  walk(ast, node => {
    if (node.type !== 'VariableDeclarator' || node.id.type !== 'Identifier' || !node.init || node.init.type !== 'ObjectExpression') return;
    for (const prop of node.init.properties) {
      if (prop.type !== 'ObjectProperty') continue;
      const id = prop.computed ? null : (prop.key.name ?? prop.key.value);
      if (id === null || prop.value.type !== 'ArrayExpression') continue;
      const vals = prop.value.elements;
      if (vals.length < 2 || !vals[0] || !vals[1] || vals[0].type !== 'StringLiteral' || vals[1].type !== 'StringLiteral') continue;
      tables['zh-cn'][String(id)] = vals[0].value;
      tables.en[String(id)] = vals[1].value;
    }
  });
  // Also support direct locale dictionaries, e.g. { 'zh-cn': {...}, en: {...} }.
  walk(ast, node => {
    if (node.type !== 'ObjectExpression') return;
    for (const prop of node.properties) {
      if (prop.type !== 'ObjectProperty') continue;
      const locale = String(prop.key.name ?? prop.key.value ?? '').toLowerCase().replace(/_/g, '-');
      if (!['zh-cn', 'zh', 'en', 'en-us'].includes(locale) || prop.value.type !== 'ObjectExpression') continue;
      const target = locale.startsWith('zh') ? 'zh-cn' : 'en';
      for (const entry of prop.value.properties) {
        if (entry.type !== 'ObjectProperty') continue;
        const id = entry.key.name ?? entry.key.value;
        if (entry.value.type === 'StringLiteral') tables[target][String(id)] = entry.value.value;
      }
    }
  });
  // Dictionaries may store language variants under each key instead of each locale.
  walk(ast, node => {
    if (node.type !== 'ObjectExpression') return;
    for (const prop of node.properties) {
      if (prop.type !== 'ObjectProperty' || prop.computed || prop.value.type !== 'ObjectExpression') continue;
      const key = prop.key.name ?? prop.key.value;
      if (key === undefined) continue;
      const variants = {};
      for (const entry of prop.value.properties) {
        if (entry.type !== 'ObjectProperty' || entry.computed || entry.value.type !== 'StringLiteral') continue;
        variants[String(entry.key.name ?? entry.key.value).toLowerCase()] = entry.value.value;
      }
      const zh = variants['zh-cn'] ?? variants['zh'] ?? variants['zh_cn'];
      const en = variants['en'] ?? variants['en-us'] ?? variants['en_us'];
      if (typeof zh === 'string') tables['zh-cn'][String(key)] ??= zh;
      if (typeof en === 'string') tables.en[String(key)] ??= en;
    }
  });
  // Common format: { key: { 'zh-CN': '涓枃', 'en-US': 'English' } } is handled above.
  // Also support language dictionaries under named exports with `zh_CN` and `en_US` keys.
  walk(ast, node => {
    if (node.type !== 'ObjectExpression') return;
    for (const prop of node.properties) {
      if (prop.type !== 'ObjectProperty' || prop.value.type !== 'ObjectExpression') continue;
      const raw = String(prop.key.name ?? prop.key.value ?? '').toLowerCase().replace(/_/g, '-');
      const target = ['zh-cn','zh'].includes(raw) ? 'zh-cn' : ['en','en-us'].includes(raw) ? 'en' : null;
      if (!target) continue;
      for (const entry of prop.value.properties) {
        if (entry.type !== 'ObjectProperty' || entry.value.type !== 'StringLiteral') continue;
        const key = entry.key.name ?? entry.key.value;
        if (key != null) tables[target][String(key)] ??= entry.value.value;
      }
    }
  });
  return tables;
}
function collectLocalSymbols(body, env) {
  const symbols = { ...env.symbols };
  const localEnv = () => ({ ...env, symbols });
  // Interpret only simple, side-effect-free AST statements. Never execute extension JS.
  function process(statements) {
    for (const stmt of statements || []) {
      if (stmt.type === 'VariableDeclaration') {
        for (const decl of stmt.declarations) if (decl.id.type === 'Identifier' && decl.init) {
          symbols[decl.id.name] = evaluate(decl.init, localEnv());
        }
      } else if (stmt.type === 'ExpressionStatement') {
        const expr = stmt.expression;
        if (expr.type === 'AssignmentExpression' && expr.operator === '=' && expr.left.type === 'Identifier') {
          symbols[expr.left.name] = evaluate(expr.right, localEnv());
        } else if (expr.type === 'CallExpression' && expr.callee.type === 'MemberExpression' && expr.callee.object.type === 'Identifier') {
          const target = expr.callee.object.name;
          const method = expr.callee.property.name;
          const array = symbols[target];
          if (Array.isArray(array) && ['push', 'unshift'].includes(method)) {
            const items = expr.arguments.map(arg => evaluate(arg, localEnv()));
            symbols[target] = method === 'push' ? [...array, ...items] : [...items, ...array];
          }
        }
      } else if (stmt.type === 'BlockStatement') process(stmt.body);
    }
  }
  if (body && body.type === 'BlockStatement') process(body.body);
  return symbols;
}
function findGetInfoReturns(ast, env) {
  const candidates = [];
  walk(ast, node => {
    const isMethod = (node.type === 'ClassMethod' || node.type === 'ObjectMethod') && node.key && (node.key.name || node.key.value) === 'getInfo';
    const isProperty = node.type === 'ObjectProperty' && node.key && (node.key.name || node.key.value) === 'getInfo' && (node.value.type === 'FunctionExpression' || node.value.type === 'ArrowFunctionExpression');
    if (!isMethod && !isProperty) return;
    const body = isMethod ? node.body : node.value.body;
    if (!body) return;
    const localSymbols = collectLocalSymbols(body, env);
    if (body.type === 'BlockStatement') {
      // Prefer direct returns to returns nested in other function bodies.
      for (const statement of body.body) if (statement.type === 'ReturnStatement' && statement.argument)
        candidates.push({ argument: statement.argument, symbols: localSymbols });
    } else candidates.push({ argument: body, symbols: localSymbols });
  });
  for (const { argument, symbols } of candidates) {
    const info = evaluate(argument, { ...env, symbols });
    if (info && typeof info === 'object' && !Array.isArray(info) && (info.blocks || info.id)) return info;
  }
  return null;
}
function parseSource(source) {
  return parser.parse(source, {
    sourceType: 'unambiguous', allowReturnOutsideFunction: true,
    plugins: ['jsx', 'classProperties', 'classPrivateProperties', 'classPrivateMethods', 'optionalChaining', 'objectRestSpread', 'dynamicImport', 'decorators-legacy', 'typescript']
  });
}
function resolveImportSymbols(ast, filename, repositoryRoot, cache, depth) {
  const imported = {};
  if (!filename || depth >= MAX_IMPORT_DEPTH) return imported;
  for (const node of ast.program.body) {
    if (node.type !== 'ImportDeclaration' || !node.source.value.startsWith('.')) continue;
    const candidate = path.resolve(path.dirname(filename), node.source.value);
    const options = [candidate, candidate + '.js', path.join(candidate, 'index.js')];
    const target = options.find(f => fs.existsSync(f) && fs.statSync(f).isFile());
    if (!target || !target.startsWith(repositoryRoot + path.sep) || cache.has(target)) continue;
    cache.add(target);
    try {
      const dependency = parseSource(fs.readFileSync(target, 'utf8'));
      const available = { ...resolveImportSymbols(dependency, target, repositoryRoot, cache, depth + 1), ...buildSymbols(dependency) };
      for (const spec of node.specifiers) {
        if (spec.type === 'ImportSpecifier') {
          const original = spec.imported.name || spec.imported.value;
          if (Object.prototype.hasOwnProperty.call(available, original)) imported[spec.local.name] = available[original];
        } else if (spec.type === 'ImportDefaultSpecifier') {
          const declaration = dependency.program.body.find(n => n.type === 'ExportDefaultDeclaration');
          if (declaration) {
            const val = evaluate(declaration.declaration, { symbols: available, messages: {} });
            if (!isUnresolved(val)) imported[spec.local.name] = val;
          }
        }
      }
    } catch (_) { /* Dependency is not statically readable. */ }
  }
  return imported;
}
// Load translation dictionaries from nearby modules without executing extension code.
// This handles projects that keep their `this.fm(key)` translations in l10n.js.
function collectAdjacentMessages(filePath, repositoryRoot) {
  const tables = { 'zh-cn': {}, en: {} };
  if (!filePath || !repositoryRoot) return tables;
  const root = path.resolve(repositoryRoot);
  const dir = path.dirname(path.resolve(filePath));
  // Search the extension's own directory, a same-name subdirectory and its
  // immediate parent. Never search unrelated extensions or execute source JS.
  const stem = path.basename(filePath, '.js');
  const directories = [dir, path.join(dir, stem), path.join(dir, 'locales'),
    path.join(dir, 'l10n'), path.dirname(dir)];
  const names = ['l10n.js','locales.js','translations.js','i18n.js',
    'lang.js','messages.js','index.js','zh-cn.js','zh_CN.js',
    'en.js','en-us.js','en_US.js'];
  const visited = new Set();
  for (const directory of directories) {
    for (const name of names) {
      if (visited.size >= MAX_LOCALE_FILES) break;
      const filename = path.resolve(directory, name);
      if (filename === path.resolve(filePath) || visited.has(filename) ||
          !(filename.startsWith(root + path.sep))) continue;
      visited.add(filename);
      try {
        if (!fs.statSync(filename).isFile()) continue;
        const ast = parseSource(fs.readFileSync(filename, 'utf8'));
        const messages = extractMessages(ast);
        for (const language of ['zh-cn', 'en'])
          Object.assign(tables[language], messages[language]);
      } catch (_) { /* Optional language files may not exist or parse. */ }
    }
  }
  return tables;
}
function extractInfo(source, locale, filePath, repositoryRoot) {
  const ast = parseSource(source);
  const imported = resolveImportSymbols(ast, filePath, repositoryRoot, new Set([filePath]), 0);
  const symbols = { ...imported, ...buildSymbols(ast) };
  const allMessages = extractMessages(ast);
  const adjacent = collectAdjacentMessages(filePath, repositoryRoot);
  for (const language of ['zh-cn', 'en']) allMessages[language] = { ...adjacent[language], ...allMessages[language] };
  const env = { symbols, messages: allMessages[locale] || {} };
  return { info: findGetInfoReturns(ast, env), messages: allMessages };
}
function normalizeBlock(block, englishBlock, info, englishInfo, relativePath, repository, category, categoryEn) {
  if (!block || typeof block !== 'object' || Array.isArray(block)) return null;
  if (!['opcode', 'blockType', 'text'].some(k => Object.prototype.hasOwnProperty.call(block, k))) return null;
  return {
    extensionId: info.id ?? null,
    extensionName: info.name ?? null,
    extensionName_en: englishInfo.name ?? info.name ?? null,
    opcode: block.opcode ?? null,
    func: block.func ?? null,
    tooltip: block.tooltip ?? block.description ?? null,
    tooltip_en: englishBlock && typeof englishBlock === 'object' ? (englishBlock.tooltip ?? englishBlock.description ?? null) : null,
    text: block.text ?? null,
    text_en: englishBlock && typeof englishBlock === 'object' ? (englishBlock.text ?? null) : null,
    blockType: block.blockType ?? null,
    arguments: block.arguments ?? {},
    branchCount: block.branchCount ?? null,
    terminal: block.terminal ?? null,
    filter: block.filter ?? null,
    category: category ?? null,
    category_en: categoryEn ?? category ?? null,
    sourceFile: relativePath,
    repository
  };
}
// Record source-level evidence for unresolved translated block labels.
// Never evaluate the extension; this diagnostic only reads Babel AST nodes.
function translationDiagnostics(source, filePath, repositoryRoot, report) {
  if (!report.unresolvedFieldDetails?.length) return [];
  const relevant = report.unresolvedFieldDetails.filter(x => ['text', 'text_en'].includes(x.field));
  if (!relevant.length) return [];
  const calls = [];
  try {
    const ast = parseSource(source);
    walk(ast, node => {
      if (node.type !== 'CallExpression') return;
      const name = sourceOf(node.callee);
      if (!/(?:^|\.)(?:fm|formatMessage|translate|t)$/.test(name)) return;
      const arg = node.arguments[0];
      const raw = arg && Number.isInteger(arg.start) && Number.isInteger(arg.end)
        ? source.slice(arg.start, arg.end).slice(0, 300) : sourceOf(arg);
      calls.push({ line: node.loc?.start?.line ?? null, callee: name,
        argument: raw, expression: source.slice(node.start, node.end).slice(0, 350) });
    });
  } catch (_) { /* The extraction report already records parse errors. */ }
  const dir = path.dirname(filePath);
  const localeFiles = [];
  for (const name of ['l10n.js','locales.js','translations.js','i18n.js',
    'locales/index.js','l10n/index.js','lang.js','messages.js']) {
    const target = path.resolve(dir, name);
    if (target.startsWith(repositoryRoot + path.sep) && fs.existsSync(target))
      localeFiles.push(path.relative(repositoryRoot, target).split(path.sep).join('/'));
  }
  const available = collectAdjacentMessages(filePath, repositoryRoot);
  const sourceMessages = (() => {
    try { return extractMessages(parseSource(source)); }
    catch (_) { return { 'zh-cn': {}, en: {} }; }
  })();
  for (const lang of ['zh-cn', 'en']) Object.assign(available[lang], sourceMessages[lang]);
  const detailedCalls = calls.slice(0, 150).map(call => {
    const key = /^(['"])(.*?)\1$/.exec(call.argument)?.[2] ?? null;
    const zh = key !== null && Object.prototype.hasOwnProperty.call(available['zh-cn'], key);
    const en = key !== null && Object.prototype.hasOwnProperty.call(available.en, key);
    return { ...call, key, zhFound: zh, enFound: en,
      reason: key === null ? 'dynamic_translation_key' :
        (!zh && !en ? 'translation_key_not_found' :
         (!zh || !en ? 'language_variant_missing' : 'translation_found_but_not_resolved')) };
  });
  return [{ file: report.file, unresolvedTextCount: relevant.filter(x => x.field === 'text').length,
    unresolvedTextEnglishCount: relevant.filter(x => x.field === 'text_en').length,
    localeFiles, translationCalls: detailedCalls,
    unresolved: relevant.map(x => ({opcode:x.opcode,field:x.field,expression:x.expression})) }];
}
function scanFile(filePath, repositoryRoot, repositoryUrl) {
  const relativePath = path.relative(repositoryRoot, filePath).split(path.sep).join('/');
  const report = { file: relativePath, status: 'unknown', blocksFound: 0, message: '' };
  try {
    const source = fs.readFileSync(filePath, 'utf8');
    const zh = extractInfo(source, 'zh-cn', filePath, repositoryRoot).info;
    const en = extractInfo(source, 'en', filePath, repositoryRoot).info || zh;
    if (!zh) {
      report.status = 'no_static_getInfo';
      report.message = 'No statically readable getInfo() return object.';
      return { blocks: [], report };
    }
    const blocks = zh.blocks;
    const englishBlocks = Array.isArray(en.blocks) ? en.blocks : [];
    if (!Array.isArray(blocks)) {
      report.status = 'dynamic_blocks';
      report.message = 'The blocks property is not a static array.';
      return { blocks: [], report };
    }
    const extracted = [];
    const issues = [];
    let category = null, categoryEn = null, unresolvedFound = false;
    for (let i = 0; i < blocks.length; i++) {
      const block = blocks[i];
      const englishBlock = englishBlocks[i] ?? null;
      if (typeof block === 'string' && block.startsWith('---')) {
        category = block.slice(3);
        categoryEn = typeof englishBlock === 'string' && englishBlock.startsWith('---') ? englishBlock.slice(3) : category;
        continue;
      }
      if (block && typeof block === 'object' && block.$spread) { unresolvedFound = true; issues.push({ index: i, reason: 'unresolved_spread', expression: block.$spread }); continue; }
      if (isUnresolved(block)) { unresolvedFound = true; issues.push({ index: i, reason: 'unresolved_fields', opcode: block && block.opcode || null }); }
      const normalized = normalizeBlock(block, englishBlock, zh, en, relativePath, repositoryUrl, category, categoryEn);
      if (normalized) extracted.push(normalized);
    }
    report.blocksFound = extracted.length;
    if (issues.length) report.issues = issues;
    report.unresolvedFieldDetails = extracted.flatMap((record, index) =>
      ['extensionId', 'opcode', 'text', 'text_en', 'blockType', 'arguments', 'tooltip', 'tooltip_en']
        .filter(field => isUnresolved(record[field]))
        .map(field => ({ index, opcode: typeof record.opcode === 'string' ? record.opcode : null,
          field, expression: record[field] })));
    if (report.unresolvedFieldDetails.length && !unresolvedFound) unresolvedFound = true;
    report.translationDiagnostics = translationDiagnostics(source, filePath, repositoryRoot, report);
    if (unresolvedFound) {
      report.status = 'partial';
      report.message = 'Some block entries contain unresolved expressions.';
    } else report.status = 'success';
    return { blocks: extracted, report };
  } catch (error) {
    report.status = 'error';
    report.message = String(error && error.message ? error.message : error).slice(0, 1000);
    return { blocks: [], report };
  }
}
function readSources() {
  if (!fs.existsSync('sources.txt')) throw new Error('sources.txt was not found.');
  return fs.readFileSync('sources.txt', 'utf8').split(/\r?\n/).map(x => x.trim()).filter(x => x && !x.startsWith('#'));
}
function listJsFiles(root) {
  const result = [];
  function visit(dir) {
    for (const entry of fs.readdirSync(dir, { withFileTypes: true }).sort((a, b) => a.name.localeCompare(b.name))) {
      if (entry.isDirectory()) {
        if (!EXCLUDED_DIRS.has(entry.name)) visit(path.join(dir, entry.name));
      } else if (entry.isFile() && entry.name.endsWith('.js') && !EXCLUDED_FILES.has(entry.name)) result.push(path.join(dir, entry.name));
    }
  }
  visit(root);
  return result;
}
function cloneRepository(url, destination) {
  cp.execFileSync('git', ['clone', '--depth', '1', url, destination], { stdio: 'pipe' });
}
// Preserve previous records even when a new static analysis cannot recover them.
// Identity includes sourceFile because the same extension may have multiple versions.
function identity(block) {
  const parts = [block.repository || '', block.sourceFile || '', block.extensionId || '', block.opcode || ''];
  if (!block.opcode) parts.push(JSON.stringify(block.text || ''), String(block.blockType || ''));
  return JSON.stringify(parts);
}
function quality(value) {
  if (value === null || value === undefined) return 0;
  if (typeof value === 'string') return value.trim() ? 2 : 0;
  if (typeof value === 'number' || typeof value === 'boolean') return 1;
  if (Array.isArray(value)) return value.reduce((n, v) => n + quality(v), 0);
  if (typeof value === 'object') {
    if ('$expression' in value || '$spread' in value) return -2;
    return Object.values(value).reduce((n, v) => n + quality(v), 0);
  }
  return 0;
}
function mergeRecord(oldRecord, newRecord) {
  const merged = { ...oldRecord, ...newRecord };
  for (const key of new Set([...Object.keys(oldRecord), ...Object.keys(newRecord)])) {
    const before = oldRecord[key], after = newRecord[key];
    if (quality(before) > quality(after)) merged[key] = before;
    else if (before && after && typeof before === 'object' && typeof after === 'object' && !Array.isArray(before) && !Array.isArray(after) && !('$expression' in before) && !('$expression' in after)) {
      merged[key] = { ...before, ...after };
      for (const field of Object.keys(before)) if (quality(before[field]) > quality(after[field])) merged[key][field] = before[field];
    }
  }
  return merged;
}
function mergeWithBaseline(current, baseline) {
  const merged = [], positions = new Map(), added = [], recovered = [], updated = [];
  for (const block of current) {
    const key = identity(block);
    if (!positions.has(key)) positions.set(key, []);
    positions.get(key).push(merged.length);
    merged.push(block);
  }
  // Match non-opcode labels by their ordinal within a source/extension, even if
  // localized text changed between runs. This prevents false historical growth.
  const specialPositions = new Map();
  const specialKey = b => JSON.stringify([b.repository || '', b.sourceFile || '', b.extensionId || '', 'no-opcode']);
  current.forEach((b, i) => {
    if (b.opcode) return;
    const key = specialKey(b);
    if (!specialPositions.has(key)) specialPositions.set(key, []);
    specialPositions.get(key).push(i);
  });
  const specialSeen = new Map();
  const seen = new Map();
  for (const oldBlock of baseline) {
    const key = identity(oldBlock), ordinal = seen.get(key) || 0;
    seen.set(key, ordinal + 1);
    const candidates = positions.get(key) || [];
    let index = ordinal < candidates.length ? candidates[ordinal] : undefined;
    if (!oldBlock.opcode) {
      const group = specialKey(oldBlock);
      const slot = specialSeen.get(group) || 0;
      specialSeen.set(group, slot + 1);
      const possible = specialPositions.get(group) || [];
      // A label's location is more stable than its translated text. Avoid
      // matching two old entries to the same current entry.
      if (slot < possible.length) index = possible[slot];
    }
    if (index !== undefined) {
      const replacement = mergeRecord(oldBlock, merged[index]);
      if (JSON.stringify(replacement) !== JSON.stringify(merged[index])) updated.push({ identity: key, reason: 'restored richer baseline fields' });
      merged[index] = replacement;
    } else {
      recovered.push({ identity: key, extensionId: oldBlock.extensionId, opcode: oldBlock.opcode, sourceFile: oldBlock.sourceFile });
      merged.push(oldBlock);
    }
  }
  const oldCounts = new Map();
  for (const b of baseline) oldCounts.set(identity(b), (oldCounts.get(identity(b)) || 0) + 1);
  const newCounts = new Map();
  for (const b of current) {
    const key = identity(b), count = (newCounts.get(key) || 0) + 1;
    newCounts.set(key, count);
    if (count > (oldCounts.get(key) || 0)) added.push({ identity: key, extensionId: b.extensionId, opcode: b.opcode, sourceFile: b.sourceFile });
  }
  return { merged, added, recovered, updated };
}
function readBaseline() {
  if (!fs.existsSync(DATABASE_FILE)) return [];
  const data = JSON.parse(fs.readFileSync(DATABASE_FILE, 'utf8').replace(/^\uFEFF/, ''));
  if (!data || !Array.isArray(data.blocks)) throw new Error('Existing database has no blocks array; refusing to overwrite it.');
  return data.blocks;
}
function main() {
  console.log('Starting CCW extension extraction v13 (static AST mode)...');
  const sources = readSources();
  if (!sources.length) throw new Error('No source repositories found in sources.txt.');
  const baseline = readBaseline();
  const allBlocks = [], allReports = [], versionReports = [];
  const temp = fs.mkdtempSync(path.join(os.tmpdir(), 'ccw-extension-'));
  try {
    sources.forEach((url, index) => {
      console.log(`Cloning source ${index + 1}: ${url}`);
      const repo = path.join(temp, `source_${index}`);
      try { cloneRepository(url, repo); }
      catch (error) {
        allReports.push({ repository: url, status: 'clone_error', blocksFound: 0, message: String(error.message || error).slice(0, 1000) });
        return;
      }
      const commit = cp.execFileSync('git', ['-C', repo, 'rev-parse', 'HEAD'], { encoding: 'utf8' }).trim();
      versionReports.push({ repository: url, commit, versionStatus: 'unknown', note: 'Only the default branch was scanned. Other branches and historical commits have not been scanned.' });
      const extensionsRoot = path.join(repo, 'extensions');
      if (!fs.existsSync(extensionsRoot) || !fs.statSync(extensionsRoot).isDirectory()) {
        allReports.push({ repository: url, status: 'missing_extensions_directory', blocksFound: 0, message: 'The repository has no extensions/ directory.' });
        return;
      }
      for (const file of listJsFiles(extensionsRoot)) {
        const result = scanFile(file, repo, url);
        result.report.repository = url;
        allReports.push(result.report);
        allBlocks.push(...result.blocks);
        console.log(`${result.report.status}: ${result.report.file} (${result.report.blocksFound} blocks)`);
      }
    });
  } finally { fs.rmSync(temp, { recursive: true, force: true }); }
  const translationDetails = allReports.flatMap(r => r.translationDiagnostics || []);
  for (const report of allReports) delete report.translationDiagnostics;
  const { merged, added, recovered, updated } = mergeWithBaseline(allBlocks, baseline);
  if (merged.length < baseline.length) throw new Error('Regression guard: merged records fell below baseline.');
  if (MINIMUM_QUALITY && merged.length < MINIMUM_QUALITY) throw new Error('Below MINIMUM_QUALITY threshold.');
  const extractedCount = allBlocks.length;
  const recoveredByFile = {};
  for (const item of recovered) recoveredByFile[item.sourceFile || '(unknown)'] = (recoveredByFile[item.sourceFile || '(unknown)'] || 0) + 1;
  const unresolvedFiles = allReports.filter(r => !['success'].includes(r.status)).map(r => ({
    file: r.file, status: r.status, blocksFound: r.blocksFound, reason: r.message, issues: r.issues || [], unresolvedFieldDetails: r.unresolvedFieldDetails || []
  }));
  allBlocks.splice(0, allBlocks.length, ...merged);
  const opcodeMap = {};
  for (const block of allBlocks) {
    if (typeof block.opcode === 'string' && block.opcode) (opcodeMap[block.opcode] ||= []).push({ sourceFile: block.sourceFile, repository: block.repository });
  }
  const duplicates = Object.fromEntries(Object.entries(opcodeMap).filter(([, locations]) => locations.length > 1));
  const uniqueTypes = new Set(allBlocks.filter(b => typeof b.extensionId === 'string' && typeof b.opcode === 'string').map(b => b.extensionId + '_' + b.opcode));
  const unresolvedFields = allBlocks.reduce((n, b) => n + ['extensionId', 'opcode', 'text', 'blockType', 'arguments'].filter(k => isUnresolved(b[k])).length, 0);
  const statusCounts = {};
  for (const report of allReports) statusCounts[report.status] = (statusCounts[report.status] || 0) + 1;
  const generatedAt = now();
  const database = { schemaVersion: 4, generatedAt, extractedThisRun: extractedCount, baselineCount: baseline.length, recoveredFromBaseline: recovered.length, sourceCount: sources.length, fileCount: allReports.length, blockCount: allBlocks.length, uniqueBlockTypes: uniqueTypes.size, unresolvedCoreFields: unresolvedFields, blocks: allBlocks, duplicateOpcodes: duplicates };
  const extractionReport = {
    generatedAt, extractedThisRun: extractedCount, baselineCount: baseline.length, recoveredFromBaseline: recovered.length, fileCount: allReports.length, uniqueBlockTypes: uniqueTypes.size, unresolvedCoreFields: unresolvedFields,
    successfulFiles: statusCounts.success || 0, partialFiles: statusCounts.partial || 0,
    dynamicFiles: statusCounts.dynamic_blocks || 0, unrecognizedFiles: statusCounts.no_static_getInfo || 0,
    errorFiles: statusCounts.error || 0, statusCounts, files: allReports
  };
  const diff = { generatedAt, baselineCount: baseline.length, extractedThisRun: extractedCount, finalCount: allBlocks.length,
    newRecords: added, recoveredFromBaseline: recovered, recoveredByFile, enrichedRecords: updated,
    note: 'Recovered records are retained from previous database, not confirmed present in current source. Compare source revisions before treating them as current.' };
  const fieldStats = {};
  const unresolvedExamples = [];
  const specialEntries = [];
  for (const [index, block] of allBlocks.entries()) {
    for (const field of ['extensionId', 'opcode', 'text', 'text_en', 'blockType', 'arguments', 'tooltip', 'tooltip_en']) {
      const value = block[field];
      const stats = (fieldStats[field] ||= { resolved: 0, absent: 0, expression: 0 });
      if (isUnresolved(value)) {
        stats.expression++;
        if (unresolvedExamples.length < 300) unresolvedExamples.push({ index, field, sourceFile: block.sourceFile, opcode: block.opcode, expression: value });
      } else if (value === null || value === undefined || value === '') stats.absent++;
      else stats.resolved++;
    }
    if (!block.opcode) specialEntries.push({ index, sourceFile: block.sourceFile, blockType: block.blockType, text: block.text });
  }
  const isUsable = b => typeof b.extensionId === 'string' && b.extensionId.length > 0 &&
    typeof b.opcode === 'string' && b.opcode.length > 0 &&
    typeof b.text === 'string' && b.text.length > 0 &&
    typeof b.blockType === 'string' && b.blockType.length > 0;
  const usable = allBlocks.filter(isUsable);
  const excluded = allBlocks.filter(b => !isUsable(b)).map(b => ({
    sourceFile: b.sourceFile, extensionId: b.extensionId, opcode: b.opcode,
    reasons: ['extensionId', 'opcode', 'text', 'blockType'].filter(k => typeof b[k] !== 'string' || !b[k])
  }));
  fs.writeFileSync(USABLE_FILE, JSON.stringify({ schemaVersion: 1, generatedAt,
    blockCount: usable.length, blocks: usable, excludedCount: excluded.length,
    excluded, note: 'Convenience view only. Full historical records remain in blocks_database.json.' }, null, 2), 'utf8');
  const unresolvedByFile = {};
  for (const block of allBlocks) {
    const file = block.sourceFile || '(unknown)';
    const entry = (unresolvedByFile[file] ||= { records: 0, unresolvedText: 0, unresolvedEnglishText: 0, unresolvedCoreFields: 0 });
    entry.records++;
    if (isUnresolved(block.text)) entry.unresolvedText++;
    if (isUnresolved(block.text_en)) entry.unresolvedEnglishText++;
    entry.unresolvedCoreFields += ['extensionId','opcode','text','blockType','arguments'].filter(k => isUnresolved(block[k])).length;
  }
  const qualityReport = { generatedAt, blockCount: allBlocks.length, usableBlockCount: usable.length, excludedFromUsable: excluded.length, fieldStats, unresolvedByFile, recoveredByFile,
    unresolvedExamples, missingOpcodeEntries: specialEntries,
    note: 'Absent tooltip is not necessarily an extraction error. Missing opcode can indicate a label/button/separator.' };
  fs.writeFileSync(QUALITY_FILE, JSON.stringify(qualityReport, null, 2), 'utf8');
  fs.writeFileSync(DIAGNOSTICS_FILE, JSON.stringify({generatedAt,
    fileCount: translationDetails.length, files: translationDetails,
    note: 'Static source call sites only; arguments are not executed. Use to implement source-specific translation rules.'}, null, 2), 'utf8');
  // Write the database last, after all reports are prepared.
  fs.writeFileSync(MISSING_FILE, JSON.stringify({ generatedAt, unresolvedFiles }, null, 2), 'utf8');
  fs.writeFileSync(DIFF_FILE, JSON.stringify(diff, null, 2), 'utf8');
  fs.writeFileSync(DATABASE_FILE, JSON.stringify(database, null, 2), 'utf8');
  fs.writeFileSync(REPORT_FILE, JSON.stringify(extractionReport, null, 2), 'utf8');
  fs.writeFileSync(VERSION_FILE, JSON.stringify(versionReports, null, 2), 'utf8');
  console.log('\nExtraction finished.');
  console.log(`Repositories: ${sources.length}`);
  console.log(`Files scanned: ${allReports.length}`);
  console.log(`Blocks extracted this run: ${extractedCount}; preserved from baseline: ${recovered.length}; final: ${allBlocks.length}`);
  console.log(`Unique block types: ${uniqueTypes.size}; unresolved core fields: ${unresolvedFields}`);
  console.log(`Successful files: ${statusCounts.success || 0}`);
  console.log(`Partial files: ${statusCounts.partial || 0}`);
  console.log(`Dynamic files: ${statusCounts.dynamic_blocks || 0}`);
  console.log(`Unrecognized files: ${statusCounts.no_static_getInfo || 0}`);
  console.log(`Errors: ${statusCounts.error || 0}`);
  console.log(`Duplicate opcodes: ${Object.keys(duplicates).length}`);
}
if (require.main === module) main();
module.exports = { identity, isUnresolved, evaluate, mergeRecord, mergeWithBaseline, extractMessages, collectAdjacentMessages, translationDiagnostics, quality };
