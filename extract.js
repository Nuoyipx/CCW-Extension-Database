
'use strict';

/**
 * CCW Extension Database Extractor v5
 * Static analysis only. Extension source files are parsed, never executed.
 */

const fs = require('fs');
const path = require('path');
const os = require('os');
const cp = require('child_process');
const parser = require('@babel/parser');

const EXTRACTOR_VERSION = '5.0.0';
const SCHEMA_VERSION = 4;
const DATABASE_FILE = 'blocks_database.json';
const REPORT_FILE = 'extraction_report.json';
const VERSION_FILE = 'version_report.json';

const EXCLUDED_DIRS = new Set([
  '.git', 'node_modules', '__pycache__', 'dist', 'build',
  'assets', 'coverage', '.next', 'vendor'
]);

const EXCLUDED_FILES = new Set([
  'webpack.config.js', 'vite.config.js', '.eslintrc.js',
  'babel.config.js', 'jest.config.js'
]);

const ENUM_GROUPS = new Set([
  'BlockType', 'ArgumentType', 'TargetType', 'MenuType',
  'Cast', 'BlockShape', 'ConnectionType'
]);

const UNRESOLVED = source => ({
  $expression: source || '<unknown>'
});

function now() {
  return new Date().toISOString();
}

function memberPath(node) {
  if (!node) return '';

  if (node.type === 'Identifier') return node.name;
  if (node.type === 'ThisExpression') return 'this';

  if (node.type === 'StringLiteral' || node.type === 'NumericLiteral') {
    return String(node.value);
  }

  if (node.type === 'MemberExpression' || node.type === 'OptionalMemberExpression') {
    const left = memberPath(node.object);
    const right = node.computed
      ? memberPath(node.property)
      : node.property.name;
    return left && right !== undefined ? `${left}.${right}` : left;
  }

  return '';
}

function sourceOf(node) {
  if (!node) return '';
  if (node.type === 'Identifier') return node.name;
  if (node.type === 'ThisExpression') return 'this';
  if (node.type === 'StringLiteral') return JSON.stringify(node.value);
  if (node.type === 'NumericLiteral') return String(node.value);
  if (node.type === 'BooleanLiteral') return String(node.value);

  if (node.type === 'MemberExpression' || node.type === 'OptionalMemberExpression') {
    return memberPath(node);
  }

  if (node.type === 'CallExpression' || node.type === 'OptionalCallExpression') {
    return `${sourceOf(node.callee)}(...)`;
  }

  if (node.type === 'NewExpression') {
    return `new ${sourceOf(node.callee)}(...)`;
  }

  if (node.type === 'TemplateLiteral') {
    return '`' + node.quasis.map(q => q.value.cooked || '').join('${...}') + '`';
  }

  return node.type || '<expression>';
}

function unresolved(node) {
  return UNRESOLVED(sourceOf(node));
}

function isUnresolved(value) {
  if (Array.isArray(value)) return value.some(isUnresolved);

  if (value && typeof value === 'object') {
    if (Object.prototype.hasOwnProperty.call(value, '$expression')) return true;
    if (Object.prototype.hasOwnProperty.call(value, '$spread')) return true;
    if (Object.prototype.hasOwnProperty.call(value, '$computed')) return true;
    return Object.values(value).some(isUnresolved);
  }

  return false;
}

function keyOf(node, env) {
  if (!node) return null;

  if (node.type === 'Identifier') return node.name;

  if (node.type === 'StringLiteral' || node.type === 'NumericLiteral') {
    return String(node.value);
  }

  if (node.type === 'TemplateLiteral' && node.expressions.length === 0) {
    return node.quasis[0].value.cooked;
  }

  const value = evaluate(node, env, 0);

  return typeof value === 'string' || typeof value === 'number'
    ? String(value)
    : null;
}

function findMessage(messages, key) {
  if (key === null || key === undefined) return undefined;

  const text = String(key);

  if (Object.prototype.hasOwnProperty.call(messages, text)) {
    return messages[text];
  }

  const lower = text.toLowerCase();
  const keys = Object.keys(messages);

  let match = keys.find(k => k.toLowerCase() === lower);

  if (match !== undefined) return messages[match];

  // Some Scratch 2 translation tables prefix labels with underscores.
  const normalized = text.replace(/^_+/, '').toLowerCase();

  match = keys.find(
    k => k.replace(/^_+/, '').toLowerCase() === normalized
  );

  return match === undefined ? undefined : messages[match];
}

function evaluateCall(node, env, depth) {
  const callee = memberPath(node.callee);
  const method = callee.split('.').pop();

  const knownTranslationMethod = [
    'formatMessage', 'fm', 'translate', 'format'
  ].includes(method);

  if (!knownTranslationMethod || !node.arguments.length) {
    return unresolved(node);
  }

  const first = node.arguments[0];
  let id = null;
  let fallback;

  if (
    first.type === 'StringLiteral' ||
    first.type === 'TemplateLiteral'
  ) {
    const value = evaluate(first, env, depth + 1);

    if (!isUnresolved(value)) id = String(value);
  } else if (first.type === 'ObjectExpression') {
    const options = evaluate(first, env, depth + 1);

    if (options && typeof options === 'object' && !isUnresolved(options)) {
      id = options.id ?? options.ID ?? options.key ?? null;
      fallback = options.default ??
        options.defaultMessage ??
        options.description;
    }
  }

  if (id === null) return unresolved(node);

  const isFm = method === 'fm';

  const lookupId = isFm && env.extensionId
    ? `${env.extensionId}.${id}`
    : id;

  const translated =
    findMessage(env.messages, lookupId) ??
    findMessage(env.messages, id);

  if (translated !== undefined) return translated;

  if (fallback !== undefined && !isUnresolved(fallback)) {
    return fallback;
  }

  // These APIs use the ID/string as a fallback when no translation exists.
  return isFm && env.extensionId ? lookupId : id;
}

function evaluate(node, env, depth = 0) {
  if (!node || depth > 32) return unresolved(node);

  const next = n => evaluate(n, env, depth + 1);

  switch (node.type) {
    case 'StringLiteral':
    case 'NumericLiteral':
    case 'BooleanLiteral':
      return node.value;

    case 'NullLiteral':
      return null;

    case 'BigIntLiteral':
      return node.value;

    case 'Identifier': {
      if (node.name === 'undefined') return null;
      if (node.name === 'NaN') return NaN;
      if (node.name === 'Infinity') return Infinity;

      if (Object.prototype.hasOwnProperty.call(env.symbols, node.name)) {
        return env.symbols[node.name];
      }

      const known = [
        'EVENT', 'COMMAND', 'REPORTER', 'BOOLEAN', 'HAT',
        'CONDITIONAL', 'LOOP', 'STRING', 'NUMBER', 'ANGLE',
        'COLOR', 'MATRIX', 'IMAGE', 'LABEL'
      ];

      if (known.includes(node.name)) return node.name;

      return unresolved(node);
    }

    case 'ArrayExpression': {
      const result = [];

      for (const element of node.elements) {
        if (!element) {
          result.push(null);
          continue;
        }

        if (element.type === 'SpreadElement') {
          const spread = next(element.argument);

          if (Array.isArray(spread)) result.push(...spread);
          else result.push({ $spread: spread });
        } else {
          result.push(next(element));
        }
      }

      return result;
    }

    case 'ObjectExpression': {
      const result = {};

      for (const prop of node.properties) {
        if (prop.type === 'SpreadElement') {
          const spread = next(prop.argument);

          if (
            spread &&
            typeof spread === 'object' &&
            !Array.isArray(spread) &&
            !isUnresolved(spread)
          ) {
            Object.assign(result, spread);
          } else {
            result.$spread = spread;
          }

          continue;
        }

        if (prop.type !== 'ObjectProperty') continue;

        const key = prop.computed
          ? keyOf(prop.key, env)
          : (prop.key.name ?? prop.key.value);

        if (key === null || key === undefined) {
          result.$computed = unresolved(prop.key);
          continue;
        }

        result[String(key)] = next(prop.value);
      }

      return result;
    }

    case 'TemplateLiteral': {
      let result = '';

      for (let i = 0; i < node.quasis.length; i++) {
        result += node.quasis[i].value.cooked ?? node.quasis[i].value.raw;

        if (i < node.expressions.length) {
          const value = next(node.expressions[i]);

          if (isUnresolved(value) || value === null || value === undefined) {
            return unresolved(node);
          }

          result += String(value);
        }
      }

      return result;
    }

    case 'MemberExpression':
    case 'OptionalMemberExpression': {
      const fullPath = memberPath(node);
      const parts = fullPath.split('.');

      if (
        parts.length >= 2 &&
        ENUM_GROUPS.has(parts[parts.length - 2])
      ) {
        return parts[parts.length - 1];
      }

      const base = next(node.object);

      const property = node.computed
        ? keyOf(node.property, env)
        : node.property.name;

      if (
        base &&
        typeof base === 'object' &&
        property !== null &&
        property !== undefined &&
        Object.prototype.hasOwnProperty.call(base, property)
      ) {
        return base[property];
      }

      return unresolved(node);
    }

    case 'CallExpression':
    case 'OptionalCallExpression':
      return evaluateCall(node, env, depth);

    case 'UnaryExpression': {
      const value = next(node.argument);

      if (isUnresolved(value)) return unresolved(node);

      if (node.operator === '-') return -Number(value);
      if (node.operator === '+') return Number(value);
      if (node.operator === '!') return !value;
      if (node.operator === '~') return ~Number(value);
      if (node.operator === 'void') return null;

      return unresolved(node);
    }

    case 'BinaryExpression':
    case 'LogicalExpression': {
      const left = next(node.left);

      if (node.operator === '&&') {
        return isUnresolved(left) ? unresolved(node) : (left ? next(node.right) : left);
      }

      if (node.operator === '||') {
        return isUnresolved(left) ? unresolved(node) : (left ? left : next(node.right));
      }

      if (node.operator === '??') {
        return isUnresolved(left) ? unresolved(node) : (left ?? next(node.right));
      }

      const right = next(node.right);

      if (isUnresolved(left) || isUnresolved(right)) {
        return unresolved(node);
      }

      if (node.operator === '+') {
        return typeof left === 'string' || typeof right === 'string'
          ? String(left) + String(right)
          : Number(left) + Number(right);
      }

      if (node.operator === '-') return Number(left) - Number(right);
      if (node.operator === '*') return Number(left) * Number(right);
      if (node.operator === '/') return Number(left) / Number(right);
      if (node.operator === '%') return Number(left) % Number(right);

      return unresolved(node);
    }

    case 'ConditionalExpression': {
      const test = next(node.test);

      if (isUnresolved(test)) return unresolved(node);

      return next(test ? node.consequent : node.alternate);
    }

    case 'TSAsExpression':
    case 'TSTypeAssertion':
    case 'TypeCastExpression':
    case 'TSNonNullExpression':
    case 'ParenthesizedExpression':
      return next(node.expression);

    case 'SequenceExpression':
      return node.expressions.length
        ? next(node.expressions[node.expressions.length - 1])
        : null;

    default:
      return unresolved(node);
  }
}

function walk(node, callback) {
  if (!node || typeof node !== 'object') return;

  if (typeof node.type === 'string') callback(node);

  for (const [key, value] of Object.entries(node)) {
    if ([
      'loc', 'start', 'end', 'leadingComments',
      'trailingComments', 'innerComments', 'extra'
    ].includes(key)) continue;

    if (Array.isArray(value)) {
      value.forEach(v => walk(v, callback));
    } else if (value && typeof value === 'object') {
      walk(value, callback);
    }
  }
}

function buildSymbols(ast) {
  const symbols = {};

  const emptyEnv = {
    symbols,
    messages: {},
    extensionId: null
  };

  walk(ast, node => {
    if (
      node.type === 'VariableDeclarator' &&
      node.id.type === 'Identifier' &&
      node.init &&
      !Object.prototype.hasOwnProperty.call(symbols, node.id.name)
    ) {
      const value = evaluate(node.init, emptyEnv, 0);

      if (!isUnresolved(value)) {
        symbols[node.id.name] = value;
      }
    }
  });

  return symbols;
}

function addLocaleObject(target, localeObject, env) {
  if (!localeObject || localeObject.type !== 'ObjectExpression') return;

  for (const entry of localeObject.properties) {
    if (entry.type !== 'ObjectProperty') continue;

    const key = entry.computed
      ? keyOf(entry.key, env)
      : (entry.key.name ?? entry.key.value);

    if (key === null || key === undefined) continue;

    const value = evaluate(entry.value, env, 0);

    if (typeof value === 'string') {
      target[String(key)] = value;
    }
  }
}

function extractMessages(ast, symbols) {
  const tables = {
    'zh-cn': {},
    en: {}
  };

  const env = {
    symbols,
    messages: {},
    extensionId: symbols.extensionId ?? null
  };

  // Pattern 1: direct locale dictionaries.
  walk(ast, node => {
    if (node.type !== 'ObjectExpression') return;

    for (const prop of node.properties) {
      if (prop.type !== 'ObjectProperty') continue;

      const locale = String(
        prop.key.name ?? prop.key.value ?? ''
      ).toLowerCase();

      if (![
        'zh-cn', 'zh', 'zh-tw',
        'en', 'en-us', 'en_us'
      ].includes(locale)) continue;

      const target = locale.startsWith('zh')
        ? 'zh-cn'
        : 'en';

      addLocaleObject(tables[target], prop.value, env);
    }
  });

  // Pattern 2: initFormatMessage({ id: [Chinese, English] }).
  walk(ast, node => {
    if (
      node.type !== 'CallExpression' ||
      !node.callee ||
      node.callee.type !== 'MemberExpression' ||
      node.callee.property.name !== 'initFormatMessage' ||
      !node.arguments.length ||
      node.arguments[0].type !== 'ObjectExpression'
    ) return;

    const prefix = typeof symbols.extensionId === 'string'
      ? symbols.extensionId
      : null;

    for (const entry of node.arguments[0].properties) {
      if (entry.type !== 'ObjectProperty') continue;

      const id = entry.computed
        ? keyOf(entry.key, env)
        : (entry.key.name ?? entry.key.value);

      if (
        id === null ||
        id === undefined ||
        entry.value.type !== 'ArrayExpression'
      ) continue;

      const values = entry.value.elements;

      if (
        values.length < 2 ||
        !values[0] ||
        !values[1] ||
        values[0].type !== 'StringLiteral' ||
        values[1].type !== 'StringLiteral'
      ) continue;

      const fullId = prefix
        ? `${prefix}.${id}`
        : String(id);

      tables['zh-cn'][fullId] = values[0].value;
      tables.en[fullId] = values[1].value;
    }
  });

  // Pattern 3: [Chinese, English] arrays in object literals.
  walk(ast, node => {
    if (node.type !== 'ObjectExpression') return;

    for (const entry of node.properties) {
      if (
        entry.type !== 'ObjectProperty' ||
        entry.value.type !== 'ArrayExpression'
      ) continue;

      const id = entry.computed
        ? keyOf(entry.key, env)
        : (entry.key.name ?? entry.key.value);

      const values = entry.value.elements;

      if (
        id === null ||
        id === undefined ||
        values.length < 2 ||
        !values[0] ||
        !values[1] ||
        values[0].type !== 'StringLiteral' ||
        values[1].type !== 'StringLiteral'
      ) continue;

      tables['zh-cn'][String(id)] = values[0].value;
      tables.en[String(id)] = values[1].value;
    }
  });

  return tables;
}

function findGetInfoReturns(ast, env) {
  const candidates = [];

  walk(ast, node => {
    const isMethod =
      (node.type === 'ClassMethod' || node.type === 'ObjectMethod') &&
      node.key &&
      node.key.name === 'getInfo';

    const isProperty =
      node.type === 'ObjectProperty' &&
      node.key &&
      node.key.name === 'getInfo' &&
      node.value &&
      (
        node.value.type === 'FunctionExpression' ||
        node.value.type === 'ArrowFunctionExpression'
      );

    if (!isMethod && !isProperty) return;

    const body = isMethod ? node.body : node.value.body;

    if (!body) return;

    walk(body, child => {
      if (
        child.type === 'ReturnStatement' &&
        child.argument &&
        child.argument.type === 'ObjectExpression'
      ) {
        candidates.push(child.argument);
      }
    });
  });

  for (const objectNode of candidates) {
    const info = evaluate(objectNode, env, 0);

    if (
      info &&
      typeof info === 'object' &&
      !Array.isArray(info)
    ) {
      return info;
    }
  }

  return null;
}

function parseSource(source) {
  const options = {
    sourceType: 'unambiguous',
    allowReturnOutsideFunction: true,
    errorRecovery: false,
    plugins: [
      'jsx', 'classProperties', 'classPrivateProperties',
      'classPrivateMethods', 'optionalChaining',
      'objectRestSpread', 'dynamicImport',
      'decorators-legacy', 'typescript',
      'importAttributes', 'topLevelAwait'
    ]
  };

  try {
    return {
      ast: parser.parse(source, options),
      normalized: false
    };
  } catch (firstError) {
    if (!source.includes('；')) throw firstError;

    const normalizedSource = normalizeFullWidthSemicolons(source);

    if (normalizedSource === source) throw firstError;

    return {
      ast: parser.parse(normalizedSource, options),
      normalized: true,
      normalizationNote:
        'Full-width semicolons outside strings/comments were normalized for parsing.'
    };
  }
}

function normalizeFullWidthSemicolons(source) {
  let state = 'code';
  let result = '';
  let escaped = false;

  for (let i = 0; i < source.length; i++) {
    const ch = source[i];
    const next = source[i + 1];

    if (state === 'code') {
      if (ch === "'") state = 'single';
      else if (ch === '"') state = 'double';
      else if (ch === '`') state = 'template';
      else if (ch === '/' && next === '/') state = 'lineComment';
      else if (ch === '/' && next === '*') state = 'blockComment';

      result += ch === '；' ? ';' : ch;
      continue;
    }

    if (
      state === 'single' ||
      state === 'double' ||
      state === 'template'
    ) {
      result += ch;

      if (escaped) {
        escaped = false;
      } else if (ch === '\\') {
        escaped = true;
      } else if (
        (state === 'single' && ch === "'") ||
        (state === 'double' && ch === '"') ||
        (state === 'template' && ch === '`')
      ) {
        state = 'code';
      }

      continue;
    }

    if (state === 'lineComment') {
      result += ch;
      if (ch === '\n') state = 'code';
      continue;
    }

    if (state === 'blockComment') {
      result += ch;

      if (ch === '*' && next === '/') {
        result += '/';
        i++;
        state = 'code';
      }
    }
  }

  return result;
}

function collectUnresolved(value, currentPath = '', output = []) {
  if (Array.isArray(value)) {
    value.forEach((item, index) => {
      collectUnresolved(
        item,
        `${currentPath}[${index}]`,
        output
      );
    });
  } else if (value && typeof value === 'object') {
    if (Object.prototype.hasOwnProperty.call(value, '$expression')) {
      output.push({
        path: currentPath || '$',
        expression: value.$expression
      });
      return output;
    }

    if (Object.prototype.hasOwnProperty.call(value, '$spread')) {
      output.push({
        path: currentPath || '$',
        expression: 'unresolved spread element'
      });
      return output;
    }

    if (Object.prototype.hasOwnProperty.call(value, '$computed')) {
      output.push({
        path: currentPath || '$',
        expression: 'unresolved computed property'
      });
      return output;
    }

    for (const [key, item] of Object.entries(value)) {
      collectUnresolved(
        item,
        currentPath ? `${currentPath}.${key}` : key,
        output
      );
    }
  }

  return output;
}

function normalizeBlock(
  block,
  englishBlock,
  info,
  englishInfo,
  relativePath,
  repository,
  category,
  categoryEn
) {
  if (
    !block ||
    typeof block !== 'object' ||
    Array.isArray(block)
  ) return null;

  if (![
    'opcode', 'blockType', 'text'
  ].some(key => Object.prototype.hasOwnProperty.call(block, key))) {
    return null;
  }

  return {
    extensionId: info.id ?? null,
    extensionName: info.name ?? null,
    extensionName_en: englishInfo.name ?? info.name ?? null,
    opcode: block.opcode ?? null,
    func: block.func ?? null,
    text: block.text ?? null,
    text_en: englishBlock && typeof englishBlock === 'object'
      ? (englishBlock.text ?? null)
      : (typeof block.text === 'string' ? block.text : null),
    blockType: block.blockType ?? null,
    arguments: block.arguments ?? {},
    branchCount: block.branchCount ?? null,
    terminal: block.terminal ?? null,
    filter: block.filter ?? null,
    tooltip: block.tooltip ?? null,
    tooltip_en: englishBlock && typeof englishBlock === 'object'
      ? (englishBlock.tooltip ?? null)
      : null,
    category: category ?? null,
    category_en: categoryEn ?? category ?? null,
    sourceFile: relativePath,
    repository
  };
}

function extractInfoFromAst(ast, locale, symbols, allMessages) {
  const env = {
    symbols,
    messages: allMessages[locale] || {},
    extensionId: typeof symbols.extensionId === 'string'
      ? symbols.extensionId
      : null
  };

  return findGetInfoReturns(ast, env);
}

function scanFile(filePath, repositoryRoot, repositoryUrl) {
  const relativePath = path
    .relative(repositoryRoot, filePath)
    .split(path.sep)
    .join('/');

  const report = {
    file: relativePath,
    status: 'unknown',
    blocksFound: 0,
    unresolvedFieldCount: 0,
    unresolvedFields: [],
    message: ''
  };

  try {
    const source = fs.readFileSync(filePath, 'utf8');
    const parsed = parseSource(source);
    const ast = parsed.ast;

    const symbols = buildSymbols(ast);
    const allMessages = extractMessages(ast, symbols);

    const zh = extractInfoFromAst(
      ast, 'zh-cn', symbols, allMessages
    );

    const en = extractInfoFromAst(
      ast, 'en', symbols, allMessages
    ) || zh;

    if (parsed.normalized) {
      report.normalizationNote = parsed.normalizationNote;
    }

    if (!zh) {
      report.status = 'no_static_getInfo';
      report.message =
        'No statically readable getInfo() return object.';

      return { blocks: [], report };
    }

    const blocks = zh.blocks;

    const englishBlocks = Array.isArray(en.blocks)
      ? en.blocks
      : [];

    if (!Array.isArray(blocks)) {
      report.status = 'dynamic_blocks';
      report.message =
        'The blocks property is not a statically readable array.';

      report.unresolvedFields = collectUnresolved(
        blocks,
        'blocks'
      );

      report.unresolvedFieldCount =
        report.unresolvedFields.length;

      return { blocks: [], report };
    }

    const extracted = [];

    let category = null;
    let categoryEn = null;

    for (let i = 0; i < blocks.length; i++) {
      const block = blocks[i];
      const englishBlock = englishBlocks[i] ?? null;

      if (
        typeof block === 'string' &&
        block.startsWith('---')
      ) {
        category = block.slice(3);

        categoryEn =
          typeof englishBlock === 'string' &&
          englishBlock.startsWith('---')
            ? englishBlock.slice(3)
            : category;

        continue;
      }

      if (
        block &&
        typeof block === 'object' &&
        block.$spread
      ) {
        report.unresolvedFields.push({
          path: `blocks[${i}]`,
          expression: 'unresolved spread element'
        });

        continue;
      }

      const unresolved = collectUnresolved(
        block,
        `blocks[${i}]`
      );

      report.unresolvedFields.push(...unresolved);

      const normalized = normalizeBlock(
        block,
        englishBlock,
        zh,
        en,
        relativePath,
        repositoryUrl,
        category,
        categoryEn
      );

      if (normalized) extracted.push(normalized);
    }

    report.blocksFound = extracted.length;
    report.unresolvedFieldCount =
      report.unresolvedFields.length;

    if (report.unresolvedFieldCount > 0) {
      report.status = 'partial';
      report.message =
        `${report.unresolvedFieldCount} unresolved field(s).`;
    } else {
      report.status = 'success';
    }

    return {
      blocks: extracted,
      report
    };
  } catch (error) {
    report.status = 'error';

    report.message = String(
      error && error.message ? error.message : error
    ).slice(0, 1000);

    return {
      blocks: [],
      report
    };
  }
}

function readSources() {
  if (!fs.existsSync('sources.txt')) {
    throw new Error('sources.txt was not found.');
  }

  return fs.readFileSync('sources.txt', 'utf8')
    .split(/\r?\n/)
    .map(line => line.trim())
    .filter(line => line && !line.startsWith('#'));
}

function listJsFiles(root) {
  const files = [];

  function visit(directory) {
    const entries = fs.readdirSync(directory, {
      withFileTypes: true
    }).sort((a, b) => a.name.localeCompare(b.name));

    for (const entry of entries) {
      const fullPath = path.join(directory, entry.name);

      if (entry.isDirectory()) {
        if (!EXCLUDED_DIRS.has(entry.name)) {
          visit(fullPath);
        }
      } else if (
        entry.isFile() &&
        entry.name.endsWith('.js') &&
        !EXCLUDED_FILES.has(entry.name)
      ) {
        files.push(fullPath);
      }
    }
  }

  visit(root);
  return files;
}

function cloneRepository(url, destination) {
  cp.execFileSync(
    'git',
    ['clone', '--depth', '1', url, destination],
    { stdio: 'pipe' }
  );
}

function main() {
  console.log(
    `Starting CCW Extension Database Extractor v${EXTRACTOR_VERSION}...`
  );

  console.log(
    'Static analysis only: extension code will not be executed.'
  );

  const sources = readSources();

  if (!sources.length) {
    throw new Error(
      'No source repositories found in sources.txt.'
    );
  }

  const allBlocks = [];
  const allReports = [];
  const versionReports = [];

  const temp = fs.mkdtempSync(
    path.join(os.tmpdir(), 'ccw-extension-')
  );

  try {
    sources.forEach((url, index) => {
      console.log(`Cloning source ${index + 1}: ${url}`);

      const repo = path.join(temp, `source_${index}`);

      try {
        cloneRepository(url, repo);
      } catch (error) {
        allReports.push({
          repository: url,
          status: 'clone_error',
          blocksFound: 0,
          unresolvedFieldCount: 0,
          unresolvedFields: [],
          message: String(
            error.message || error
          ).slice(0, 1000)
        });

        return;
      }

      const commit = cp.execFileSync(
        'git',
        ['-C', repo, 'rev-parse', 'HEAD'],
        { encoding: 'utf8' }
      ).trim();

      versionReports.push({
        repository: url,
        commit,
        extractorVersion: EXTRACTOR_VERSION,
        versionStatus: 'default_branch_only',
        note:
          'Only the repository default branch was scanned; other branches and historical commits were not scanned.'
      });

      const extensionsRoot = path.join(
        repo,
        'extensions'
      );

      if (
        !fs.existsSync(extensionsRoot) ||
        !fs.statSync(extensionsRoot).isDirectory()
      ) {
        allReports.push({
          repository: url,
          status: 'missing_extensions_directory',
          blocksFound: 0,
          unresolvedFieldCount: 0,
          unresolvedFields: [],
          message:
            'The repository has no extensions/ directory.'
        });

        return;
      }

      for (const file of listJsFiles(extensionsRoot)) {
        const result = scanFile(file, repo, url);

        result.report.repository = url;

        allReports.push(result.report);
        allBlocks.push(...result.blocks);

        console.log(
          `${result.report.status}: ${result.report.file} ` +
          `(${result.report.blocksFound} blocks, ` +
          `${result.report.unresolvedFieldCount || 0} unresolved fields)`
        );
      }
    });
  } finally {
    fs.rmSync(temp, {
      recursive: true,
      force: true
    });
  }

  const opcodeMap = {};

  for (const block of allBlocks) {
    if (
      typeof block.opcode === 'string' &&
      block.opcode
    ) {
      (opcodeMap[block.opcode] ||= []).push({
        extensionId: block.extensionId,
        sourceFile: block.sourceFile,
        repository: block.repository
      });
    }
  }

  const duplicateOpcodes = Object.fromEntries(
    Object.entries(opcodeMap).filter(
      ([, locations]) => locations.length > 1
    )
  );

  const statusCounts = {};
  let unresolvedFieldCount = 0;

  for (const report of allReports) {
    statusCounts[report.status] =
      (statusCounts[report.status] || 0) + 1;

    unresolvedFieldCount +=
      report.unresolvedFieldCount || 0;
  }

  const generatedAt = now();

  const database = {
    schemaVersion: SCHEMA_VERSION,
    extractorVersion: EXTRACTOR_VERSION,
    generatedAt,
    sourceCount: sources.length,
    fileCount: allReports.length,
    blockCount: allBlocks.length,
    unresolvedFieldCount,
    blocks: allBlocks,
    duplicateOpcodes
  };

  const extractionReport = {
    schemaVersion: SCHEMA_VERSION,
    extractorVersion: EXTRACTOR_VERSION,
    generatedAt,
    fileCount: allReports.length,
    blockCount: allBlocks.length,
    unresolvedFieldCount,
    successfulFiles: statusCounts.success || 0,
    partialFiles: statusCounts.partial || 0,
    dynamicFiles: statusCounts.dynamic_blocks || 0,
    unrecognizedFiles:
      statusCounts.no_static_getInfo || 0,
    errorFiles: statusCounts.error || 0,
    statusCounts,
    files: allReports
  };

  fs.writeFileSync(
    DATABASE_FILE,
    JSON.stringify(database, null, 2),
    'utf8'
  );

  fs.writeFileSync(
    REPORT_FILE,
    JSON.stringify(extractionReport, null, 2),
    'utf8'
  );

  fs.writeFileSync(
    VERSION_FILE,
    JSON.stringify(versionReports, null, 2),
    'utf8'
  );

  console.log('\nExtraction finished.');
  console.log(`Repositories: ${sources.length}`);
  console.log(`Files scanned: ${allReports.length}`);
  console.log(`Blocks extracted: ${allBlocks.length}`);
  console.log(`Unresolved fields: ${unresolvedFieldCount}`);
  console.log(`Successful files: ${statusCounts.success || 0}`);
  console.log(`Partial files: ${statusCounts.partial || 0}`);
  console.log(`Dynamic files: ${statusCounts.dynamic_blocks || 0}`);
  console.log(`Unrecognized files: ${statusCounts.no_static_getInfo || 0}`);
  console.log(`Errors: ${statusCounts.error || 0}`);
  console.log(`Duplicate opcodes: ${Object.keys(duplicateOpcodes).length}`);
}

main();
