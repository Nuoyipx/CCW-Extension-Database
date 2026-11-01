
'use strict';

/**
 * CCW Extension Database Extractor v6
 *
 * Static analysis only.
 * Extension source code is parsed, never executed.
 */

const fs = require('fs');
const path = require('path');
const os = require('os');
const cp = require('child_process');
const parser = require('@babel/parser');

const EXTRACTOR_VERSION = '6.0.0';
const SCHEMA_VERSION = 5;

const DATABASE_FILE = 'blocks_database.json';
const REPORT_FILE = 'extraction_report.json';
const VERSION_FILE = 'version_report.json';

const EXCLUDED_DIRS = new Set([
  '.git', 'node_modules', '__pycache__', 'dist',
  'build', 'assets', 'coverage', '.next', 'vendor'
]);

const EXCLUDED_FILES = new Set([
  'webpack.config.js', 'vite.config.js',
  '.eslintrc.js', 'babel.config.js', 'jest.config.js'
]);

const ENUM_GROUPS = new Set([
  'BlockType', 'ArgumentType', 'TargetType',
  'MenuType', 'Cast', 'BlockShape', 'ConnectionType'
]);

const MARKERS = {
  unknown: '$expression',
  dynamic: '$dynamic',
  function: '$function',
  spread: '$dynamicSpread'
};

function marker(kind, expression) {
  return { [MARKERS[kind]]: expression || '<unknown>' };
}

function isMarker(value, kind) {
  return Boolean(
    value &&
    typeof value === 'object' &&
    Object.prototype.hasOwnProperty.call(value, MARKERS[kind])
  );
}

function hasMarker(value, kind) {
  if (isMarker(value, kind)) return true;

  if (Array.isArray(value)) {
    return value.some(item => hasMarker(item, kind));
  }

  if (value && typeof value === 'object') {
    return Object.values(value).some(
      item => hasMarker(item, kind)
    );
  }

  return false;
}

function now() {
  return new Date().toISOString();
}

function memberPath(node) {
  if (!node) return '';

  if (node.type === 'Identifier') return node.name;
  if (node.type === 'ThisExpression') return 'this';

  if (
    node.type === 'StringLiteral' ||
    node.type === 'NumericLiteral'
  ) {
    return String(node.value);
  }

  if (
    node.type === 'MemberExpression' ||
    node.type === 'OptionalMemberExpression'
  ) {
    const left = memberPath(node.object);
    const right = node.computed
      ? memberPath(node.property)
      : node.property.name;

    return left && right !== undefined
      ? `${left}.${right}`
      : left;
  }

  return '';
}

function sourceOf(node) {
  if (!node) return '<unknown>';

  if (node.type === 'Identifier') return node.name;
  if (node.type === 'ThisExpression') return 'this';

  if (node.type === 'StringLiteral') {
    return JSON.stringify(node.value);
  }

  if (node.type === 'NumericLiteral') {
    return String(node.value);
  }

  if (node.type === 'BooleanLiteral') {
    return String(node.value);
  }

  if (
    node.type === 'MemberExpression' ||
    node.type === 'OptionalMemberExpression'
  ) {
    return memberPath(node);
  }

  if (
    node.type === 'CallExpression' ||
    node.type === 'OptionalCallExpression'
  ) {
    return `${sourceOf(node.callee)}(...)`;
  }

  if (node.type === 'TemplateLiteral') {
    return '`' + node.quasis
      .map(q => q.value.cooked || '')
      .join('${...}') + '`';
  }

  if (
    node.type === 'ArrowFunctionExpression' ||
    node.type === 'FunctionExpression' ||
    node.type === 'ObjectMethod' ||
    node.type === 'ClassMethod'
  ) {
    return '<function>';
  }

  return node.type || '<expression>';
}

function isUnknown(value) {
  return hasMarker(value, 'unknown') ||
    hasMarker(value, 'spread');
}

function isTranslationKey(value) {
  return typeof value === 'string' &&
    /^[A-Za-z0-9_-]+(?:\.[A-Za-z0-9_-]+)+$/.test(value);
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
      value.forEach(child => walk(child, callback));
    } else if (value && typeof value === 'object') {
      walk(value, callback);
    }
  }
}

/**
 * Walk a function body without entering nested functions.
 */
function walkFunctionBody(node, callback, isRoot = true) {
  if (!node || typeof node !== 'object') return;

  if (!isRoot && [
    'FunctionDeclaration',
    'FunctionExpression',
    'ArrowFunctionExpression',
    'ClassMethod',
    'ObjectMethod'
  ].includes(node.type)) {
    return;
  }

  if (typeof node.type === 'string') callback(node);

  for (const [key, value] of Object.entries(node)) {
    if ([
      'loc', 'start', 'end', 'leadingComments',
      'trailingComments', 'innerComments', 'extra'
    ].includes(key)) continue;

    if (Array.isArray(value)) {
      value.forEach(child =>
        walkFunctionBody(child, callback, false)
      );
    } else if (value && typeof value === 'object') {
      walkFunctionBody(value, callback, false);
    }
  }
}

function parseSource(source) {
  const options = {
    sourceType: 'unambiguous',
    allowReturnOutsideFunction: true,
    errorRecovery: false,
    plugins: [
      'jsx',
      'classProperties',
      'classPrivateProperties',
      'classPrivateMethods',
      'optionalChaining',
      'objectRestSpread',
      'dynamicImport',
      'decorators-legacy',
      'typescript',
      'importAttributes',
      'topLevelAwait'
    ]
  };

  try {
    return {
      ast: parser.parse(source, options),
      normalized: false
    };
  } catch (firstError) {
    if (!source.includes('；')) throw firstError;

    const normalized = normalizeFullWidthSemicolons(source);

    if (normalized === source) throw firstError;

    return {
      ast: parser.parse(normalized, options),
      normalized: true
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

    result += ch;

    if (state === 'lineComment' && ch === '\n') {
      state = 'code';
    }

    if (
      state === 'blockComment' &&
      ch === '*' &&
      next === '/'
    ) {
      result += '/';
      i++;
      state = 'code';
    }
  }

  return result;
}

function findMessage(messages, key) {
  if (key === null || key === undefined) return undefined;

  const text = String(key);

  if (Object.prototype.hasOwnProperty.call(messages, text)) {
    return messages[text];
  }

  const lower = text.toLowerCase();

  const found = Object.keys(messages).find(
    item => item.toLowerCase() === lower
  );

  return found === undefined ? undefined : messages[found];
}

function evaluate(node, env, depth = 0) {
  if (!node || depth > 40) {
    return marker('unknown', sourceOf(node));
  }

  const next = child => evaluate(child, env, depth + 1);

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

      if (
        Object.prototype.hasOwnProperty.call(
          env.symbols,
          node.name
        )
      ) {
        return env.symbols[node.name];
      }

      if ([
        'EVENT', 'COMMAND', 'REPORTER', 'BOOLEAN',
        'HAT', 'CONDITIONAL', 'LOOP', 'STRING',
        'NUMBER', 'ANGLE', 'COLOR', 'MATRIX',
        'IMAGE', 'LABEL'
      ].includes(node.name)) {
        return node.name;
      }

      return marker('unknown', node.name);
    }

    case 'ThisExpression':
      return marker('dynamic', 'this');

    case 'ArrayExpression': {
      const result = [];

      for (const element of node.elements) {
        if (!element) {
          result.push(null);
          continue;
        }

        if (element.type === 'SpreadElement') {
          const spread = next(element.argument);

          if (Array.isArray(spread)) {
            result.push(...spread);
          } else {
            result.push(
              marker(
                'spread',
                sourceOf(element.argument)
              )
            );
          }
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
            !isUnknown(spread)
          ) {
            Object.assign(result, spread);
          } else {
            result.$spread = sourceOf(prop.argument);
          }

          continue;
        }

        if (prop.type === 'ObjectMethod') {
          const key = prop.computed
            ? null
            : (prop.key.name ?? prop.key.value);

          if (key !== null && key !== undefined) {
            result[String(key)] = marker(
              'function',
              sourceOf(prop)
            );
          }

          continue;
        }

        if (prop.type !== 'ObjectProperty') continue;

        const key = prop.computed
          ? evaluate(prop.key, env, depth + 1)
          : (prop.key.name ?? prop.key.value);

        if (
          key === null ||
          key === undefined ||
          typeof key === 'object'
        ) {
          result.$computed = sourceOf(prop.key);
          continue;
        }

        result[String(key)] = next(prop.value);
      }

      return result;
    }

    case 'TemplateLiteral': {
      let result = '';

      for (let i = 0; i < node.quasis.length; i++) {
        result += node.quasis[i].value.cooked ??
          node.quasis[i].value.raw;

        if (i < node.expressions.length) {
          const value = next(node.expressions[i]);

          if (
            value &&
            typeof value === 'object'
          ) {
            return marker(
              'dynamic',
              sourceOf(node)
            );
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

      if (node.object.type === 'ThisExpression') {
        return marker('dynamic', fullPath);
      }

      const base = next(node.object);

      const property = node.computed
        ? next(node.property)
        : node.property.name;

      if (
        base &&
        typeof base === 'object' &&
        !Array.isArray(base) &&
        typeof property !== 'object' &&
        Object.prototype.hasOwnProperty.call(base, property)
      ) {
        return base[property];
      }

      return marker('unknown', fullPath);
    }

    case 'CallExpression':
    case 'OptionalCallExpression':
      return evaluateCall(node, env, depth);

    case 'ArrowFunctionExpression':
    case 'FunctionExpression':
    case 'ObjectMethod':
    case 'ClassMethod':
      return marker('function', sourceOf(node));

    case 'UnaryExpression': {
      const value = next(node.argument);

      if (value && typeof value === 'object') {
        return marker('dynamic', sourceOf(node));
      }

      if (node.operator === '-') return -Number(value);
      if (node.operator === '+') return Number(value);
      if (node.operator === '!') return !value;
      if (node.operator === '~') return ~Number(value);
      if (node.operator === 'void') return null;

      return marker('unknown', sourceOf(node));
    }

    case 'BinaryExpression':
    case 'LogicalExpression': {
      const left = next(node.left);

      if (node.operator === '&&') {
        if (typeof left === 'object') {
          return marker('dynamic', sourceOf(node));
        }
        return left ? next(node.right) : left;
      }

      if (node.operator === '||') {
        if (typeof left === 'object') {
          return marker('dynamic', sourceOf(node));
        }
        return left || next(node.right);
      }

      if (node.operator === '??') {
        if (typeof left === 'object') {
          return marker('dynamic', sourceOf(node));
        }
        return left ?? next(node.right);
      }

      const right = next(node.right);

      if (
        (left && typeof left === 'object') ||
        (right && typeof right === 'object')
      ) {
        return marker('dynamic', sourceOf(node));
      }

      switch (node.operator) {
        case '+':
          return typeof left === 'string' ||
            typeof right === 'string'
            ? String(left) + String(right)
            : Number(left) + Number(right);
        case '-':
          return Number(left) - Number(right);
        case '*':
          return Number(left) * Number(right);
        case '/':
          return Number(left) / Number(right);
        case '%':
          return Number(left) % Number(right);
        default:
          return marker('unknown', sourceOf(node));
      }
    }

    case 'ConditionalExpression': {
      const test = next(node.test);

      if (test && typeof test === 'object') {
        return marker('dynamic', sourceOf(node));
      }

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
      return marker('unknown', sourceOf(node));
  }
}

function evaluateCall(node, env, depth) {
  const callee = memberPath(node.callee);
  const method = callee.split('.').pop();

  if (!node.arguments.length) {
    return marker('dynamic', sourceOf(node));
  }

  const first = node.arguments[0];
  const firstValue = evaluate(first, env, depth + 1);

  if ([
    'formatMessage',
    'fm',
    'translate',
    'format'
  ].includes(method)) {
    let id = null;
    let fallback;

    if (typeof firstValue === 'string') {
      id = firstValue;
    } else if (
      firstValue &&
      typeof firstValue === 'object' &&
      !isUnknown(firstValue)
    ) {
      id = firstValue.id ??
        firstValue.ID ??
        firstValue.key ??
        null;

      fallback = firstValue.default ??
        firstValue.defaultMessage ??
        firstValue.description;
    }

    if (id === null) {
      return marker('dynamic', sourceOf(node));
    }

    const prefix = method === 'fm'
      ? env.extensionId
      : null;

    const fullId = prefix &&
      !String(id).startsWith(`${prefix}.`)
      ? `${prefix}.${id}`
      : String(id);

    const translated =
      findMessage(env.messages, fullId) ??
      findMessage(env.messages, id);

    if (translated !== undefined) return translated;

    if (fallback !== undefined) return fallback;

    return fullId;
  }

  if (
    method === '__dataNameOrObjMsg' &&
    typeof firstValue === 'string'
  ) {
    const id = `defaultValue.${firstValue}Name`;
    const fullId = env.extensionId
      ? `${env.extensionId}.${id}`
      : id;

    return findMessage(env.messages, fullId) ??
      findMessage(env.messages, id) ??
      marker('dynamic', sourceOf(node));
  }

  if (
    method === 'concat' &&
    node.callee.object
  ) {
    const base = evaluate(node.callee.object, env, depth + 1);

    if (Array.isArray(base)) {
      const result = [...base];

      for (const argument of node.arguments) {
        const value = evaluate(argument, env, depth + 1);

        if (Array.isArray(value)) result.push(...value);
        else result.push(value);
      }

      return result;
    }
  }

  return marker('dynamic', sourceOf(node));
}

/**
 * Parse local default imports such as:
 * import l10n from './l10n.js'
 *
 * Imported source is parsed but never executed.
 */
function loadImportedDefault(filePath, depth = 0) {
  if (depth > 3 || !fs.existsSync(filePath)) {
    return marker('unknown', `import:${filePath}`);
  }

  try {
    const parsed = parseSource(
      fs.readFileSync(filePath, 'utf8')
    );

    const symbols = buildTopLevelSymbols(
      parsed.ast,
      path.dirname(filePath),
      depth + 1
    );

    for (const statement of parsed.ast.program.body) {
      if (statement.type !== 'ExportDefaultDeclaration') {
        continue;
      }

      return evaluate(
        statement.declaration,
        {
          symbols,
          messages: {},
          extensionId: null
        }
      );
    }
  } catch (_) {
    return marker('unknown', `import:${filePath}`);
  }

  return marker('unknown', `import:${filePath}`);
}

function buildTopLevelSymbols(ast, directory, importDepth = 0) {
  const symbols = {};

  for (const statement of ast.program.body) {
    if (statement.type === 'ImportDeclaration') {
      const defaultSpecifier = statement.specifiers.find(
        specifier => specifier.type === 'ImportDefaultSpecifier'
      );

      if (!defaultSpecifier) continue;

      const importedPath = path.resolve(
        directory,
        statement.source.value
      );

      symbols[defaultSpecifier.local.name] =
        loadImportedDefault(importedPath, importDepth);
    }
  }

  const declarations = [];

  for (const statement of ast.program.body) {
    if (statement.type !== 'VariableDeclaration') continue;

    for (const declaration of statement.declarations) {
      if (
        declaration.id.type === 'Identifier' &&
        declaration.init
      ) {
        declarations.push(declaration);
      }
    }
  }

  for (let pass = 0; pass < 8; pass++) {
    let changed = false;

    for (const declaration of declarations) {
      const name = declaration.id.name;

      if (
        Object.prototype.hasOwnProperty.call(symbols, name)
      ) continue;

      const value = evaluate(
        declaration.init,
        {
          symbols,
          messages: {},
          extensionId: null
        }
      );

      if (!isUnknown(value)) {
        symbols[name] = value;
        changed = true;
      }
    }

    if (!changed) break;
  }

  return symbols;
}

function addLocaleObject(target, localeObject, env) {
  if (
    !localeObject ||
    typeof localeObject !== 'object' ||
    Array.isArray(localeObject)
  ) return;

  for (const [key, value] of Object.entries(localeObject)) {
    if (typeof value === 'string') {
      target[key] = value;
    }
  }
}

function extractMessages(ast, symbols, extensionId) {
  const tables = {
    'zh-cn': {},
    en: {}
  };

  const env = {
    symbols,
    messages: {},
    extensionId
  };

  // Runtime.getFormatMessage({ 'zh-cn': {...}, en: {...} })
  walk(ast, node => {
    if (
      node.type !== 'CallExpression' ||
      !node.arguments.length ||
      memberPath(node.callee).split('.').pop() !==
        'getFormatMessage'
    ) return;

    const value = evaluate(
      node.arguments[0],
      env
    );

    if (!value || typeof value !== 'object') return;

    for (const [locale, dictionary] of Object.entries(value)) {
      const normalized = locale.toLowerCase();

      if (normalized.startsWith('zh')) {
        addLocaleObject(tables['zh-cn'], dictionary, env);
      } else if (normalized.startsWith('en')) {
        addLocaleObject(tables.en, dictionary, env);
      }
    }
  });

  // initFormatMessage(importedDictionary)
  walk(ast, node => {
    if (
      node.type !== 'CallExpression' ||
      memberPath(node.callee).split('.').pop() !==
        'initFormatMessage' ||
      !node.arguments.length
    ) return;

    const dictionary = evaluate(
      node.arguments[0],
      env
    );

    if (
      !dictionary ||
      typeof dictionary !== 'object' ||
      Array.isArray(dictionary)
    ) return;

    for (const [key, pair] of Object.entries(dictionary)) {
      if (
        !Array.isArray(pair) ||
        pair.length < 2 ||
        typeof pair[0] !== 'string' ||
        typeof pair[1] !== 'string'
      ) continue;

      const fullKey = extensionId
        ? `${extensionId}.${key}`
        : key;

      tables['zh-cn'][fullKey] = pair[0];
      tables.en[fullKey] = pair[1];
    }
  });

  return tables;
}

function getMethodBody(node) {
  if (
    node.type === 'ClassMethod' ||
    node.type === 'ObjectMethod'
  ) {
    return node.body;
  }

  if (
    node.type === 'ObjectProperty' &&
    node.value &&
    (
      node.value.type === 'FunctionExpression' ||
      node.value.type === 'ArrowFunctionExpression'
    )
  ) {
    return node.value.body;
  }

  return null;
}

function collectReturnObjects(body) {
  const results = [];

  if (!body) return results;

  if (body.type === 'ObjectExpression') {
    results.push(body);
    return results;
  }

  walkFunctionBody(body, node => {
    if (
      node.type === 'ReturnStatement' &&
      node.argument &&
      node.argument.type === 'ObjectExpression'
    ) {
      results.push(node.argument);
    }
  });

  return results;
}

function buildLocalSymbols(body, env) {
  const declarations = [];

  walkFunctionBody(body, node => {
    if (
      node.type === 'VariableDeclarator' &&
      node.id.type === 'Identifier' &&
      node.init
    ) {
      declarations.push(node);
    }
  });

  const symbols = { ...env.symbols };

  for (let pass = 0; pass < 10; pass++) {
    let changed = false;

    for (const declaration of declarations) {
      const name = declaration.id.name;

      const value = evaluate(
        declaration.init,
        {
          ...env,
          symbols
        }
      );

      if (
        !Object.prototype.hasOwnProperty.call(symbols, name) ||
        isUnknown(symbols[name])
      ) {
        if (!isUnknown(value)) {
          symbols[name] = value;
          changed = true;
        }
      }
    }

    if (!changed) break;
  }

  return symbols;
}

function extractInfo(ast, baseSymbols, messages, extensionId) {
  const candidates = [];

  walk(ast, node => {
    const isGetInfo =
      (
        node.type === 'ClassMethod' ||
        node.type === 'ObjectMethod'
      ) &&
      node.key &&
      node.key.name === 'getInfo';

    const isGetInfoProperty =
      node.type === 'ObjectProperty' &&
      node.key &&
      node.key.name === 'getInfo' &&
      node.value &&
      (
        node.value.type === 'FunctionExpression' ||
        node.value.type === 'ArrowFunctionExpression'
      );

    if (!isGetInfo && !isGetInfoProperty) return;

    const body = getMethodBody(node);
    if (!body) return;

    const env = {
      symbols: buildLocalSymbols(
        body,
        {
          symbols: baseSymbols,
          messages,
          extensionId
        }
      ),
      messages,
      extensionId
    };

    for (const objectNode of collectReturnObjects(body)) {
      const info = evaluate(objectNode, env);

      if (
        info &&
        typeof info === 'object' &&
        !Array.isArray(info)
      ) {
        candidates.push(info);
      }
    }
  });

  return candidates.find(
    candidate => Array.isArray(candidate.blocks)
  ) || candidates[0] || null;
}

function collectDiagnostics(value, currentPath = '', output = {}) {
  if (!output.unknown) output.unknown = [];
  if (!output.dynamic) output.dynamic = [];
  if (!output.functions) output.functions = [];
  if (!output.spreads) output.spreads = [];

  if (Array.isArray(value)) {
    value.forEach((item, index) => {
      collectDiagnostics(
        item,
        `${currentPath}[${index}]`,
        output
      );
    });

    return output;
  }

  if (!value || typeof value !== 'object') {
    return output;
  }

  if (isMarker(value, 'unknown')) {
    output.unknown.push({
      path: currentPath,
      expression: value.$expression
    });
    return output;
  }

  if (isMarker(value, 'dynamic')) {
    output.dynamic.push({
      path: currentPath,
      expression: value.$dynamic
    });
    return output;
  }

  if (isMarker(value, 'function')) {
    output.functions.push({
      path: currentPath,
      expression: value.$function
    });
    return output;
  }

  if (isMarker(value, 'spread')) {
    output.spreads.push({
      path: currentPath,
      expression: value.$dynamicSpread
    });
    return output;
  }

  for (const [key, item] of Object.entries(value)) {
    collectDiagnostics(
      item,
      currentPath ? `${currentPath}.${key}` : key,
      output
    );
  }

  return output;
}

function removeFunctions(value) {
  if (isMarker(value, 'function')) return undefined;

  if (Array.isArray(value)) {
    return value.map(item => {
      const cleaned = removeFunctions(item);
      return cleaned === undefined ? null : cleaned;
    });
  }

  if (value && typeof value === 'object') {
    const result = {};

    for (const [key, item] of Object.entries(value)) {
      const cleaned = removeFunctions(item);

      if (cleaned !== undefined) {
        result[key] = cleaned;
      }
    }

    return result;
  }

  return value;
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
  ].some(key =>
    Object.prototype.hasOwnProperty.call(block, key)
  )) {
    return null;
  }

  const cleanBlock = removeFunctions(block);
  const cleanEnglish = englishBlock &&
    typeof englishBlock === 'object'
    ? removeFunctions(englishBlock)
    : null;

  const text = cleanBlock.text ?? null;
  let textEn = cleanEnglish
    ? (cleanEnglish.text ?? null)
    : null;

  if (isTranslationKey(textEn)) textEn = null;

  let finalCategoryEn = categoryEn ?? null;

  // Never expose an untranslated internal key as English text.
  if (isTranslationKey(finalCategoryEn)) {
    finalCategoryEn = null;
  }

  const diagnostics = collectDiagnostics(block);

  return {
    extensionId: info.id ?? null,
    extensionName: info.name ?? null,
    extensionName_en: englishInfo.name ?? null,

    opcode: cleanBlock.opcode ?? null,
    func: cleanBlock.func ?? null,

    text,
    text_en: textEn,

    blockType: cleanBlock.blockType ?? null,
    arguments: cleanBlock.arguments ?? {},

    branchCount: cleanBlock.branchCount ?? null,
    terminal: cleanBlock.terminal ?? null,
    filter: cleanBlock.filter ?? null,

    tooltip: cleanBlock.tooltip ?? null,
    tooltip_en: cleanEnglish
      ? (cleanEnglish.tooltip ?? null)
      : null,

    category: category ?? null,
    category_en: finalCategoryEn,

    fieldStatus: {
      dynamic: diagnostics.dynamic,
      functions: diagnostics.functions,
      unknown: diagnostics.unknown,
      dynamicSpreads: diagnostics.spreads
    },

    sourceFile: relativePath,
    repository
  };
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
    dynamicFieldCount: 0,
    functionFieldCount: 0,
    unresolvedFields: [],
    dynamicFields: [],
    functionFields: [],
    message: ''
  };

  try {
    const parsed = parseSource(
      fs.readFileSync(filePath, 'utf8')
    );

    const ast = parsed.ast;

    const symbols = buildTopLevelSymbols(
      ast,
      path.dirname(filePath)
    );

    const extensionId =
      typeof symbols.extensionId === 'string'
        ? symbols.extensionId
        : null;

    const allMessages = extractMessages(
      ast,
      symbols,
      extensionId
    );

    const zh = extractInfo(
      ast,
      symbols,
      allMessages['zh-cn'],
      extensionId
    );

    const en = extractInfo(
      ast,
      symbols,
      allMessages.en,
      extensionId
    ) || zh;

    if (parsed.normalized) {
      report.normalizationNote =
        'Full-width semicolons outside strings/comments were normalized.';
    }

    if (!zh) {
      report.status = 'no_static_getInfo';
      report.message =
        'No statically readable getInfo() return object.';
      return { blocks: [], report };
    }

    if (!Array.isArray(zh.blocks)) {
      report.status = 'dynamic_blocks';
      report.message =
        'The blocks property is not a statically readable array.';

      report.unresolvedFields = collectDiagnostics(
        zh.blocks,
        'blocks'
      ).unknown;

      report.unresolvedFieldCount =
        report.unresolvedFields.length;

      return { blocks: [], report };
    }

    const englishBlocks = Array.isArray(en.blocks)
      ? en.blocks
      : [];

    const extracted = [];

    let category = null;
    let categoryEn = null;
    let categoryUncertain = false;

    for (let i = 0; i < zh.blocks.length; i++) {
      const block = zh.blocks[i];
      const englishBlock = englishBlocks[i] ?? null;

      if (typeof block === 'string' && block.startsWith('---')) {
        category = block.slice(3);

        categoryEn =
          typeof englishBlock === 'string' &&
          englishBlock.startsWith('---')
            ? englishBlock.slice(3)
            : null;

        categoryUncertain = false;
        continue;
      }

      if (isMarker(block, 'spread')) {
        report.dynamicFields.push({
          path: `blocks[${i}]`,
          expression: block.$dynamicSpread
        });

        category = null;
        categoryEn = null;
        categoryUncertain = true;
        continue;
      }

      const diagnostics = collectDiagnostics(
        block,
        `blocks[${i}]`
      );

      report.unresolvedFields.push(
        ...diagnostics.unknown
      );

      report.dynamicFields.push(
        ...diagnostics.dynamic
      );

      report.functionFields.push(
        ...diagnostics.functions
      );

      report.dynamicFields.push(
        ...diagnostics.spreads
      );

      const normalized = normalizeBlock(
        block,
        englishBlock,
        zh,
        en,
        relativePath,
        repositoryUrl,
        categoryUncertain ? null : category,
        categoryUncertain ? null : categoryEn
      );

      if (normalized) extracted.push(normalized);
    }

    report.blocksFound = extracted.length;

    report.unresolvedFieldCount =
      report.unresolvedFields.length;

    report.dynamicFieldCount =
      report.dynamicFields.length;

    report.functionFieldCount =
      report.functionFields.length;

    if (report.unresolvedFieldCount > 0) {
      report.status = 'partial';
      report.message =
        `${report.unresolvedFieldCount} unknown field(s).`;
    } else if (report.dynamicFieldCount > 0) {
      report.status = 'dynamic_fields';
      report.message =
        `${report.dynamicFieldCount} runtime-dependent field(s).`;
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
    'Static analysis only: extension source code will not be executed.'
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
          dynamicFieldCount: 0,
          functionFieldCount: 0,
          unresolvedFields: [],
          dynamicFields: [],
          functionFields: [],
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
          'Only the repository default branch was scanned.'
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
          dynamicFieldCount: 0,
          functionFieldCount: 0,
          unresolvedFields: [],
          dynamicFields: [],
          functionFields: [],
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
          `${result.report.unresolvedFieldCount} unknown, ` +
          `${result.report.dynamicFieldCount} dynamic)`
        );
      }
    });
  } finally {
    fs.rmSync(temp, {
      recursive: true,
      force: true
    });
  }

  const globalOpcodeMap = {};
  const namespacedOpcodeMap = {};

  for (const block of allBlocks) {
    if (
      typeof block.opcode !== 'string' ||
      !block.opcode
    ) continue;

    const location = {
      extensionId: block.extensionId,
      sourceFile: block.sourceFile,
      repository: block.repository
    };

    (globalOpcodeMap[block.opcode] ||= []).push(location);

    const namespace = [
      block.repository,
      block.extensionId || '<no-extension-id>',
      block.opcode
    ].join('::');

    (namespacedOpcodeMap[namespace] ||= []).push(location);
  }

  const duplicateOpcodes = Object.fromEntries(
    Object.entries(globalOpcodeMap).filter(
      ([, locations]) => locations.length > 1
    )
  );

  const duplicateNamespacedOpcodes = Object.fromEntries(
    Object.entries(namespacedOpcodeMap).filter(
      ([, locations]) => locations.length > 1
    )
  );

  const statusCounts = {};

  let unresolvedFieldCount = 0;
  let dynamicFieldCount = 0;
  let functionFieldCount = 0;

  for (const report of allReports) {
    statusCounts[report.status] =
      (statusCounts[report.status] || 0) + 1;

    unresolvedFieldCount +=
      report.unresolvedFieldCount || 0;

    dynamicFieldCount +=
      report.dynamicFieldCount || 0;

    functionFieldCount +=
      report.functionFieldCount || 0;
  }

  const missingFields = {
    opcode: 0,
    text: 0,
    text_en: 0,
    blockType: 0,
    arguments: 0,
    category: 0,
    category_en: 0
  };

  for (const block of allBlocks) {
    for (const field of Object.keys(missingFields)) {
      const value = block[field];

      if (
        value === null ||
        value === undefined ||
        value === ''
      ) {
        missingFields[field]++;
      }
    }
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
    dynamicFieldCount,
    functionFieldCount,

    blocks: allBlocks,

    duplicateOpcodes,
    duplicateNamespacedOpcodes,

    quality: {
      missingFields
    }
  };

  const extractionReport = {
    schemaVersion: SCHEMA_VERSION,
    extractorVersion: EXTRACTOR_VERSION,
    generatedAt,

    fileCount: allReports.length,
    blockCount: allBlocks.length,

    unresolvedFieldCount,
    dynamicFieldCount,
    functionFieldCount,

    successfulFiles: statusCounts.success || 0,
    partialFiles: statusCounts.partial || 0,
    dynamicFiles: statusCounts.dynamic_blocks || 0,
    dynamicFieldFiles: statusCounts.dynamic_fields || 0,
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

  console.log('');
  console.log('Extraction completed.');
  console.log(`Files: ${allReports.length}`);
  console.log(`Blocks: ${allBlocks.length}`);
  console.log(`Unknown fields: ${unresolvedFieldCount}`);
  console.log(`Dynamic fields: ${dynamicFieldCount}`);
  console.log(`Function fields: ${functionFieldCount}`);
  console.log(`Errors: ${statusCounts.error || 0}`);
}

main();
