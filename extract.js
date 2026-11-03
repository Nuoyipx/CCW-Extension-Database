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
      if (isFormat && node.arguments.length && node.arguments[0].type === 'StringLiteral') {
        const id = node.arguments[0].value;
        const translated = env.messages[id] ?? env.messages[id.toLowerCase()];
        if (translated !== undefined) return translated;
      }
      const name = sourceOf(callee);
      if (['Scratch.translate', 'translate', 'formatMessage', 'Scratch.translate.formatMessage'].includes(name) && node.arguments.length) {
        const arg = next(node.arguments[0]);
        if (typeof arg === 'string') return env.messages[arg] ?? arg;
        if (arg && typeof arg === 'object' && typeof arg.default === 'string') return env.messages[arg.id] ?? arg.default;
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
      const locale = String(prop.key.name ?? prop.key.value ?? '').toLowerCase();
      if (!['zh-cn', 'zh', 'en', 'en-us'].includes(locale) || prop.value.type !== 'ObjectExpression') continue;
      const target = locale.startsWith('zh') ? 'zh-cn' : 'en';
      for (const entry of prop.value.properties) {
        if (entry.type !== 'ObjectProperty') continue;
        const id = entry.key.name ?? entry.key.value;
        if (entry.value.type === 'StringLiteral') tables[target][String(id)] = entry.value.value;
      }
    }
  });
  return tables;
}
function findGetInfoReturns(ast, env) {
  const candidates = [];
  walk(ast, node => {
    const isMethod = (node.type === 'ClassMethod' || node.type === 'ObjectMethod') && node.key && (node.key.name || node.key.value) === 'getInfo';
    const isProperty = node.type === 'ObjectProperty' && node.key && (node.key.name || node.key.value) === 'getInfo' && (node.value.type === 'FunctionExpression' || node.value.type === 'ArrowFunctionExpression');
    if (!isMethod && !isProperty) return;
    const body = isMethod ? node.body : node.value.body;
    if (!body) return;
    const localSymbols = { ...env.symbols };
    walk(body, child => {
      if (child.type === 'VariableDeclarator' && child.id.type === 'Identifier' && child.init) {
        const val = evaluate(child.init, { ...env, symbols: localSymbols });
        if (!isUnresolved(val)) localSymbols[child.id.name] = val;
      }
      if (child.type === 'ReturnStatement' && child.argument)
        candidates.push({ argument: child.argument, symbols: { ...localSymbols } });
    });
  });
  for (const { argument, symbols } of candidates) {
    const info = evaluate(argument, { ...env, symbols });
    if (info && typeof info === 'object' && !Array.isArray(info) && (info.blocks || info.id)) return info;
  }
  return null;
}
function extractInfo(source, locale) {
  const ast = parser.parse(source, {
    sourceType: 'unambiguous', allowReturnOutsideFunction: true,
    plugins: ['jsx', 'classProperties', 'classPrivateProperties', 'classPrivateMethods', 'optionalChaining', 'objectRestSpread', 'dynamicImport', 'decorators-legacy', 'typescript']
  });
  const symbols = buildSymbols(ast);
  const allMessages = extractMessages(ast);
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
function scanFile(filePath, repositoryRoot, repositoryUrl) {
  const relativePath = path.relative(repositoryRoot, filePath).split(path.sep).join('/');
  const report = { file: relativePath, status: 'unknown', blocksFound: 0, message: '' };
  try {
    const source = fs.readFileSync(filePath, 'utf8');
    const zh = extractInfo(source, 'zh-cn').info;
    const en = extractInfo(source, 'en').info || zh;
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
    let category = null, categoryEn = null, unresolvedFound = false;
    for (let i = 0; i < blocks.length; i++) {
      const block = blocks[i];
      const englishBlock = englishBlocks[i] ?? null;
      if (typeof block === 'string' && block.startsWith('---')) {
        category = block.slice(3);
        categoryEn = typeof englishBlock === 'string' && englishBlock.startsWith('---') ? englishBlock.slice(3) : category;
        continue;
      }
      if (block && typeof block === 'object' && block.$spread) { unresolvedFound = true; continue; }
      if (isUnresolved(block)) unresolvedFound = true;
      const normalized = normalizeBlock(block, englishBlock, zh, en, relativePath, repositoryUrl, category, categoryEn);
      if (normalized) extracted.push(normalized);
    }
    report.blocksFound = extracted.length;
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
  const seen = new Map();
  for (const oldBlock of baseline) {
    const key = identity(oldBlock), ordinal = seen.get(key) || 0;
    seen.set(key, ordinal + 1);
    const candidates = positions.get(key) || [];
    if (ordinal < candidates.length) {
      const index = candidates[ordinal];
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
  console.log('Starting CCW extension extraction (static AST mode)...');
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
  const { merged, added, recovered, updated } = mergeWithBaseline(allBlocks, baseline);
  if (merged.length < baseline.length) throw new Error('Regression guard: merged records fell below baseline.');
  if (MINIMUM_QUALITY && merged.length < MINIMUM_QUALITY) throw new Error('Below MINIMUM_QUALITY threshold.');
  const extractedCount = allBlocks.length;
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
    newRecords: added, recoveredFromBaseline: recovered, enrichedRecords: updated,
    note: 'Recovered records are retained from previous database, not confirmed present in current source. Compare source revisions before treating them as current.' };
  // Write the database last, after all reports are prepared.
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
main();
