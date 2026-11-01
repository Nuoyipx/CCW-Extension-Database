'use strict';

/**
 * CCW Extension Database Extractor
 * Version: 7.0.0
 *
 * 静态分析扩展源码，不执行任何扩展代码。
 */

const fs = require('fs');
const path = require('path');
const os = require('os');
const { execFileSync } = require('child_process');
const parser = require('@babel/parser');

const EXTRACTOR_VERSION = '7.0.0';
const SCHEMA_VERSION = 6;

const ROOT = process.cwd();
const SOURCES_FILE = path.join(ROOT, 'sources.txt');

const OUTPUT_DATABASE = path.join(ROOT, 'blocks_database.json');
const OUTPUT_REPORT = path.join(ROOT, 'extraction_report.json');
const OUTPUT_VERSION = path.join(ROOT, 'version_report.json');

const ENUM_VALUES = {
  BlockType: {
    BOOLEAN: 'Boolean',
    BUTTON: 'button',
    COMMAND: 'command',
    CONDITIONAL: 'conditional',
    EVENT: 'event',
    HAT: 'hat',
    LOOP: 'loop',
    REPORTER: 'reporter',
    LABEL: 'label'
  },
  ArgumentType: {
    ANGLE: 'angle',
    BOOLEAN: 'Boolean',
    COLOR: 'color',
    IMAGE: 'image',
    MATRIX: 'matrix',
    NUMBER: 'number',
    STRING: 'string',
    NOTE: 'note',
    TEXT: 'string'
  },
  TargetType: {
    SPRITE: 'sprite',
    STAGE: 'stage'
  }
};

const DYNAMIC = value => ({ $dynamic: value || 'dynamic expression' });
const UNKNOWN = value => ({ $expression: value || 'unknown expression' });
const FUNCTION = value => ({ $function: value || 'function' });

function isObject(value) {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function isMarker(value) {
  return isObject(value) &&
    ('$dynamic' in value || '$expression' in value || '$function' in value);
}

function clone(value) {
  return JSON.parse(JSON.stringify(value));
}

function getSource(node) {
  if (!node) return '';
  return node.extra && node.extra.raw
    ? node.extra.raw
    : node.type;
}

/**
 * 将字符串和注释之外的全角分号转换为普通分号。
 */
function normalizeFullWidthSemicolons(source) {
  let output = '';
  let state = 'normal';
  let quote = '';
  let escaped = false;

  for (let i = 0; i < source.length; i++) {
    const c = source[i];
    const next = source[i + 1];

    if (state === 'lineComment') {
      output += c;
      if (c === '\n') state = 'normal';
      continue;
    }

    if (state === 'blockComment') {
      output += c;
      if (c === '*' && next === '/') {
        output += next;
        i++;
        state = 'normal';
      }
      continue;
    }

    if (state === 'string' || state === 'template') {
      output += c;

      if (escaped) {
        escaped = false;
        continue;
      }

      if (c === '\\') {
        escaped = true;
        continue;
      }

      if (c === quote) {
        state = 'normal';
        quote = '';
      }
      continue;
    }

    if (c === '/' && next === '/') {
      output += '//';
      i++;
      state = 'lineComment';
      continue;
    }

    if (c === '/' && next === '*') {
      output += '/*';
      i++;
      state = 'blockComment';
      continue;
    }

    if (c === '"' || c === "'") {
      state = 'string';
      quote = c;
      output += c;
      continue;
    }

    if (c === '`') {
      state = 'template';
      quote = '`';
      output += c;
      continue;
    }

    output += c === '；' ? ';' : c;
  }

  return output;
}

function parseSource(source, filename) {
  const normalized = normalizeFullWidthSemicolons(source);

  return parser.parse(normalized, {
    sourceType: 'unambiguous',
    allowReturnOutsideFunction: true,
    errorRecovery: false,
    plugins: [
      'jsx',
      'typescript',
      'classProperties',
      'classPrivateProperties',
      'classPrivateMethods',
      'objectRestSpread',
      'optionalChaining',
      'dynamicImport',
      'decorators-legacy'
    ]
  });
}

function memberName(node) {
  if (!node) return null;

  if (node.type === 'Identifier') return node.name;

  if (node.type === 'StringLiteral') return node.value;

  if (node.type === 'MemberExpression' ||
      node.type === 'OptionalMemberExpression') {
    const left = memberName(node.object);
    const right = node.computed
      ? memberName(node.property)
      : node.property.name;

    return left && right ? `${left}.${right}` : null;
  }

  return null;
}

function expressionName(node) {
  if (!node) return 'unknown';

  if (node.type === 'Identifier') return node.name;

  if (node.type === 'ThisExpression') return 'this';

  if (node.type === 'MemberExpression') {
    return memberName(node) || 'member expression';
  }

  if (node.type === 'CallExpression') {
    return `${expressionName(node.callee)}(...)`;
  }

  return node.type;
}

function evaluate(node, env = {}, context = {}, depth = 0) {
  if (!node || depth > 35) return UNKNOWN('maximum evaluation depth');

  const next = child => evaluate(child, env, context, depth + 1);

  switch (node.type) {
    case 'StringLiteral':
    case 'NumericLiteral':
    case 'BooleanLiteral':
      return node.value;

    case 'NullLiteral':
      return null;

    case 'BigIntLiteral':
      return Number(node.value);

    case 'Identifier':
      if (node.name === 'undefined') return null;
      if (node.name === 'NaN') return null;
      if (Object.prototype.hasOwnProperty.call(env, node.name)) {
        return env[node.name];
      }
      return UNKNOWN(node.name);

    case 'ThisExpression':
      return DYNAMIC('this');

    case 'ArrowFunctionExpression':
    case 'FunctionExpression':
    case 'FunctionDeclaration':
      return FUNCTION('function');

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
            result.push(DYNAMIC(`spread: ${expressionName(element.argument)}`));
          }
        } else {
          result.push(next(element));
        }
      }

      return result;
    }

    case 'ObjectExpression': {
      const result = {};

      for (const property of node.properties) {
        if (property.type === 'SpreadElement') {
          const spread = next(property.argument);

          if (isObject(spread) && !isMarker(spread)) {
            Object.assign(result, spread);
          } else {
            result.$spread = expressionName(property.argument);
          }
          continue;
        }

        if (property.type !== 'ObjectProperty' &&
            property.type !== 'ObjectMethod') continue;

        const key = property.computed
          ? next(property.key)
          : property.key.name !== undefined
            ? property.key.name
            : property.key.value;

        if (typeof key !== 'string' && typeof key !== 'number') continue;

        result[key] = property.type === 'ObjectMethod'
          ? FUNCTION('object method')
          : next(property.value);
      }

      return result;
    }

    case 'TemplateLiteral': {
      let result = '';

      for (let i = 0; i < node.quasis.length; i++) {
        result += node.quasis[i].value.cooked || '';

        if (i < node.expressions.length) {
          const value = next(node.expressions[i]);

          if (typeof value === 'string' || typeof value === 'number') {
            result += value;
          } else {
            return DYNAMIC('template literal with dynamic expression');
          }
        }
      }

      return result;
    }

    case 'UnaryExpression': {
      const value = next(node.argument);

      if (isMarker(value)) return value;

      switch (node.operator) {
        case '!': return !value;
        case '+': return Number(value);
        case '-': return -Number(value);
        case '~': return ~Number(value);
        case 'void': return null;
        default: return UNKNOWN(`unary ${node.operator}`);
      }
    }

    case 'BinaryExpression':
    case 'LogicalExpression': {
      const left = next(node.left);
      const right = next(node.right);

      if (isMarker(left) || isMarker(right)) {
        return DYNAMIC('binary expression');
      }

      try {
        switch (node.operator) {
          case '+': return left + right;
          case '-': return left - right;
          case '*': return left * right;
          case '/': return left / right;
          case '%': return left % right;
          case '**': return left ** right;
          case '===': return left === right;
          case '!==': return left !== right;
          case '==': return left == right; // 静态分析
          case '!=': return left != right;
          case '>': return left > right;
          case '<': return left < right;
          case '>=': return left >= right;
          case '<=': return left <= right;
          case '&&': return left && right;
          case '||': return left || right;
          case '??': return left ?? right;
          default: return UNKNOWN(`operator ${node.operator}`);
        }
      } catch {
        return UNKNOWN('binary expression');
      }
    }

    case 'ConditionalExpression': {
      const test = next(node.test);

      if (isMarker(test)) return DYNAMIC('conditional expression');

      return test ? next(node.consequent) : next(node.alternate);
    }

    case 'MemberExpression':
    case 'OptionalMemberExpression': {
      const fullName = memberName(node);

      if (fullName) {
        const parts = fullName.split('.');
        const enumIndex = parts.length - 2;
        const enumName = parts[enumIndex];
        const member = parts[parts.length - 1];

        if (ENUM_VALUES[enumName] &&
            Object.prototype.hasOwnProperty.call(ENUM_VALUES[enumName], member)) {
          return ENUM_VALUES[enumName][member];
        }

        if (parts.length === 2 &&
            Object.prototype.hasOwnProperty.call(env, parts[0])) {
          const object = env[parts[0]];

          if (isObject(object) &&
              Object.prototype.hasOwnProperty.call(object, parts[1])) {
            return object[parts[1]];
          }
        }
      }

      const object = next(node.object);
      const property = node.computed
        ? next(node.property)
        : node.property.name;

      if (isObject(object) && !isMarker(object) &&
          Object.prototype.hasOwnProperty.call(object, property)) {
        return object[property];
      }

      if (Array.isArray(object) && property === 'length') {
        return object.length;
      }

      return UNKNOWN(fullName || 'member expression');
    }

    case 'CallExpression':
    case 'OptionalCallExpression':
      return evaluateCall(node, env, context, depth + 1);

    case 'TSAsExpression':
    case 'TSTypeAssertion':
    case 'TSNonNullExpression':
    case 'ParenthesizedExpression':
      return next(node.expression);

    case 'SpreadElement':
      return next(node.argument);

    default:
      return UNKNOWN(node.type);
  }
}

/**
 * 只处理可安全静态推导的函数调用。
 * 不执行源码中的任何函数。
 */
function evaluateCall(node, env, context, depth) {
  const callee = node.callee;
  const name = memberName(callee) || expressionName(callee);

  // Biter：this.b(blockObject, function)
  // 只解析第一个参数，绝不处理第二个函数。
  if (name === 'this.b' || name === 'b') {
    if (node.arguments.length >= 1) {
      return evaluate(node.arguments[0], env, context, depth + 1);
    }
  }

  // Feishu：cloneReporterBlocks(...)
  if (name.endsWith('cloneReporterBlocks') ||
      name === 'cloneReporterBlocks') {
    return expandCloneReporterBlocks(node, env, context, depth + 1);
  }

  // 常见本地化函数
  const isTranslation =
    /(^|\.)(formatMessage|fm|translate|getText|format)$/.test(name);

  if (isTranslation) {
    const first = node.arguments[0];

    if (first && first.type === 'StringLiteral') {
      const key = first.value;
      const translated = context.messages && context.messages[key];

      if (translated !== undefined) return translated;

      return DYNAMIC(`translation:${key}`);
    }

    if (first && first.type === 'ObjectExpression') {
      const object = evaluate(first, env, context, depth + 1);

      if (isObject(object)) {
        const key = object.id || object.default || object.message;

        if (typeof key === 'string') {
          const translated = context.messages && context.messages[key];

          if (translated !== undefined) return translated;

          return DYNAMIC(`translation:${key}`);
        }
      }
    }

    return DYNAMIC(`translation call: ${name}`);
  }

  // 静态字符串拼接
  if (name.endsWith('.concat') || name === 'concat') {
    const object = callee.type === 'MemberExpression'
      ? evaluate(callee.object, env, context, depth + 1)
      : null;

    const args = node.arguments.map(arg =>
      evaluate(arg, env, context, depth + 1)
    );

    if (typeof object === 'string' &&
        args.every(v => typeof v === 'string' || typeof v === 'number')) {
      return object + args.join('');
    }
  }

  return DYNAMIC(`call: ${name}`);
}

function expandCloneReporterBlocks(node, env, context, depth) {
  const args = node.arguments;

  const sourceBlocks = evaluate(args[0], env, context, depth + 1);
  const blockTypes = evaluate(args[1], env, context, depth + 1);
  const hiddenTypes = args[2]
    ? evaluate(args[2], env, context, depth + 1)
    : [];

  const beforeBlockType = args[3]
    ? evaluate(args[3], env, context, depth + 1)
    : null;

  if (!Array.isArray(sourceBlocks) || !Array.isArray(blockTypes)) {
    return DYNAMIC('cloneReporterBlocks arguments are not static arrays');
  }

  if (!blockTypes.every(type => typeof type === 'string')) {
    return DYNAMIC('cloneReporterBlocks blockTypes are dynamic');
  }

  const hidden = Array.isArray(hiddenTypes) ? hiddenTypes : [];
  const result = [];

  for (const block of sourceBlocks) {
    if (!isObject(block) || typeof block.opcode !== 'string') continue;

    for (const type of blockTypes) {
      if (!type) continue;

      const copy = clone(block);

      if (beforeBlockType !== type) {
        copy.opcode = `${copy.opcode}${type}`;
      }

      copy.blockType = type;
      copy.hideFromPalette = hidden.includes(type);

      result.push(copy);
    }
  }

  return result;
}

/**
 * 提取可静态读取的语言字典。
 */
function extractMessages(ast) {
  const messages = {};

  function walk(node) {
    if (!node || typeof node !== 'object') return;

    if (node.type === 'ObjectExpression') {
      const properties = {};

      for (const property of node.properties) {
        if (property.type !== 'ObjectProperty') continue;

        const key = property.key.name !== undefined
          ? property.key.name
          : property.key.value;

        if (typeof key !== 'string') continue;

        const value = property.value;

        if (value.type === 'StringLiteral') {
          properties[key] = value.value;
        } else if (
          value.type === 'ArrayExpression' &&
          value.elements.every(e => e && e.type === 'StringLiteral')
        ) {
          properties[key] = value.elements.map(e => e.value);
        }
      }

      Object.assign(messages, properties);
    }

    for (const key of Object.keys(node)) {
      if (key === 'loc' || key === 'start' || key === 'end') continue;

      const value = node[key];

      if (Array.isArray(value)) {
        for (const child of value) {
          if (child && typeof child.type === 'string') walk(child);
        }
      } else if (value && typeof value.type === 'string') {
        walk(value);
      }
    }
  }

  walk(ast);
  return messages;
}

function buildTopLevelSymbols(ast, context) {
  const env = {};

  for (const statement of ast.program.body) {
    if (statement.type === 'VariableDeclaration') {
      for (const declaration of statement.declarations) {
        if (declaration.id.type !== 'Identifier') continue;

        env[declaration.id.name] = evaluate(
          declaration.init,
          env,
          context
        );
      }
    }

    if (statement.type === 'ImportDeclaration') {
      for (const specifier of statement.specifiers) {
        if (specifier.type === 'ImportDefaultSpecifier') {
          env[specifier.local.name] = DYNAMIC('imported default');
        } else if (specifier.type === 'ImportSpecifier') {
          env[specifier.local.name] = DYNAMIC('imported symbol');
        }
      }
    }
  }

  return env;
}

function collectLocalSymbols(functionNode, parentEnv, context) {
  const env = { ...parentEnv };

  if (!functionNode || !functionNode.body) return env;

  function walk(node) {
    if (!node || typeof node !== 'object') return;

    if (node !== functionNode.body &&
        (
          node.type === 'FunctionDeclaration' ||
          node.type === 'FunctionExpression' ||
          node.type === 'ArrowFunctionExpression'
        )) {
      return;
    }

    if (node.type === 'VariableDeclarator' &&
        node.id.type === 'Identifier') {
      env[node.id.name] = evaluate(node.init, env, context);
    }

    for (const key of Object.keys(node)) {
      if (key === 'loc' || key === 'start' || key === 'end') continue;

      const value = node[key];

      if (Array.isArray(value)) {
        for (const child of value) {
          if (child && typeof child.type === 'string') walk(child);
        }
      } else if (value && typeof value.type === 'string') {
        walk(value);
      }
    }
  }

  walk(functionNode.body);
  return env;
}

function findGetInfoMethods(ast) {
  const found = [];

  function walk(node) {
    if (!node || typeof node !== 'object') return;

    if (
      (node.type === 'ClassMethod' ||
       node.type === 'ObjectMethod' ||
       node.type === 'ClassPrivateMethod') &&
      node.key &&
      node.key.name === 'getInfo'
    ) {
      found.push(node);
    }

    if (
      node.type === 'ObjectProperty' &&
      node.key &&
      node.key.name === 'getInfo' &&
      node.value &&
      (
        node.value.type === 'FunctionExpression' ||
        node.value.type === 'ArrowFunctionExpression'
      )
    ) {
      found.push(node.value);
    }

    for (const key of Object.keys(node)) {
      if (key === 'loc' || key === 'start' || key === 'end') continue;

      const value = node[key];

      if (Array.isArray(value)) {
        for (const child of value) {
          if (child && typeof child.type === 'string') walk(child);
        }
      } else if (value && typeof value.type === 'string') {
        walk(value);
      }
    }
  }

  walk(ast);
  return found;
}

function collectReturnObjects(functionNode) {
  const results = [];

  function walk(node) {
    if (!node || typeof node !== 'object') return;

    if (node !== functionNode.body &&
        (
          node.type === 'FunctionDeclaration' ||
          node.type === 'FunctionExpression' ||
          node.type === 'ArrowFunctionExpression'
        )) {
      return;
    }

    if (node.type === 'ReturnStatement' && node.argument) {
      results.push(node.argument);
      return;
    }

    for (const key of Object.keys(node)) {
      if (key === 'loc' || key === 'start' || key === 'end') continue;

      const value = node[key];

      if (Array.isArray(value)) {
        for (const child of value) {
          if (child && typeof child.type === 'string') walk(child);
        }
      } else if (value && typeof value.type === 'string') {
        walk(value);
      }
    }
  }

  if (functionNode.body && functionNode.body.type === 'BlockStatement') {
    walk(functionNode.body);
  } else if (functionNode.body) {
    results.push(functionNode.body);
  }

  return results;
}

function findProperty(object, key) {
  if (!isObject(object)) return undefined;
  return object[key];
}

function getInfoObjects(ast, env, context) {
  const methods = findGetInfoMethods(ast);
  const objects = [];

  for (const method of methods) {
    const localEnv = collectLocalSymbols(method, env, context);
    const returns = collectReturnObjects(method);

    for (const expression of returns) {
      const value = evaluate(expression, localEnv, context);

      if (isObject(value)) objects.push(value);
    }
  }

  return objects;
}

function normalizeBlock(block, extension, filePath, index) {
  if (!isObject(block)) {
    return {
      index,
      invalidBlock: true,
      raw: block
    };
  }

  const result = clone(block);

  result.extensionName = extension.name;
  result.extensionId = extension.id;
  result.sourceFile = filePath;
  result.index = index;

  if (typeof result.opcode !== 'string') {
    result.opcode = null;
  }

  if (typeof result.text !== 'string') {
    if (result.text === undefined) result.text = null;
  }

  if (typeof result.text_en !== 'string' &&
      result.text_en !== null &&
      result.text_en !== undefined) {
    result.text_en = null;
  }

  if (typeof result.category !== 'string' &&
      result.category !== null &&
      result.category !== undefined) {
    result.category = null;
  }

  if (typeof result.category_en !== 'string' &&
      result.category_en !== null &&
      result.category_en !== undefined) {
    result.category_en = null;
  }

  if (result.arguments === undefined) {
    result.arguments = {};
  }

  if (result.tooltip === undefined) result.tooltip = null;
  if (result.tooltip_en === undefined) result.tooltip_en = null;

  return result;
}

function getExtensionInfo(info, relativePath) {
  const basename = path.basename(relativePath, path.extname(relativePath));

  const id = typeof info.id === 'string'
    ? info.id
    : basename;

  const name = typeof info.name === 'string'
    ? info.name
    : basename;

  return { id, name };
}

/**
 * LPP 专用静态注册链分析。
 *
 * 只识别 Extension.register / Category.register / Button /
 * Reporter / Command 的结构，不执行任何函数。
 */
function evaluateLppExpression(node, env, depth = 0) {
  if (!node || depth > 60) return DYNAMIC('LPP expression depth');

  if (node.type === 'ParenthesizedExpression') {
    return evaluateLppExpression(node.expression, env, depth + 1);
  }

  if (node.type === 'Identifier') {
    return env[node.name] || UNKNOWN(node.name);
  }

  if (node.type === 'StringLiteral') return node.value;

  if (node.type === 'ArrayExpression') {
    return node.elements.map(element =>
      evaluateLppExpression(element, env, depth + 1)
    );
  }

  if (node.type === 'NewExpression') {
    const name = expressionName(node.callee);
    const args = node.arguments.map(arg =>
      arg.type === 'ArrowFunctionExpression' ||
      arg.type === 'FunctionExpression'
        ? FUNCTION('LPP lazy function')
        : evaluateLppExpression(arg, env, depth + 1)
    );

    if (name.endsWith('Extension')) {
      return { __lpp: 'Extension', blocks: [] };
    }

    if (name.endsWith('Category')) {
      return {
        __lpp: 'Category',
        label: args[0] || DYNAMIC('category label'),
        entries: []
      };
    }

    if (name.endsWith('Button')) {
      return {
        __lpp: 'Button',
        args
      };
    }

    return {
      __lpp: 'Block',
      type: name,
      args
    };
  }

  if (node.type === 'CallExpression') {
    const callee = node.callee;

    if (callee.type === 'MemberExpression' &&
        callee.property.name === 'register') {
      const target = evaluateLppExpression(
        callee.object,
        env,
        depth + 1
      );

      const args = node.arguments.map(arg =>
        evaluateLppExpression(arg, env, depth + 1)
      );

      if (isObject(target) && target.__lpp === 'Extension') {
        const item = args[0];

        if (item && item.__lpp === 'Category') {
          target.blocks.push(item);
        } else if (item && item.__lpp === 'Button') {
          target.blocks.push(item);
        }

        return target;
      }

      if (isObject(target) && target.__lpp === 'Category') {
        const opcode = args[0];
        const block = args[1];

        if (typeof opcode === 'string' && isObject(block)) {
          target.entries.push({
            opcode,
            block
          });
        }

        return target;
      }

      return target;
    }

    const name = expressionName(callee);

    if (
      name.includes('Reporter') ||
      name.includes('Command') ||
      name.includes('Boolean') ||
      name.includes('Hat') ||
      name.includes('Loop')
    ) {
      return {
        __lpp: 'Block',
        type: name,
        args: node.arguments.map(arg =>
          arg.type === 'ArrowFunctionExpression' ||
          arg.type === 'FunctionExpression'
            ? FUNCTION('LPP block function')
            : evaluateLppExpression(arg, env, depth + 1)
        )
      };
    }

    return DYNAMIC(`LPP call: ${name}`);
  }

  if (node.type === 'MemberExpression') {
    return expressionName(node);
  }

  if (node.type === 'ArrowFunctionExpression' ||
      node.type === 'FunctionExpression') {
    return FUNCTION('LPP lazy function');
  }

  return DYNAMIC(`LPP ${node.type}`);
}

function findDefineExtension(ast) {
  let found = null;

  function walk(node) {
    if (!node || typeof node !== 'object' || found) return;

    if (
      node.type === 'FunctionDeclaration' &&
      node.id &&
      node.id.name === 'defineExtension'
    ) {
      found = node;
      return;
    }

    if (
      node.type === 'VariableDeclarator' &&
      node.id.type === 'Identifier' &&
      node.id.name === 'defineExtension' &&
      node.init &&
      (
        node.init.type === 'ArrowFunctionExpression' ||
        node.init.type === 'FunctionExpression'
      )
    ) {
      found = node.init;
      return;
    }

    for (const key of Object.keys(node)) {
      if (key === 'loc' || key === 'start' || key === 'end') continue;

      const value = node[key];

      if (Array.isArray(value)) {
        for (const child of value) walk(child);
      } else if (value && typeof value.type === 'string') {
        walk(value);
      }
    }
  }

  walk(ast);
  return found;
}

function extractLppBlocks(ast) {
  const defineExtension = findDefineExtension(ast);

  if (!defineExtension) {
    return {
      blocks: [],
      recognized: false
    };
  }

  const returns = collectReturnObjects(defineExtension);
  let extension = null;

  for (const expression of returns) {
    const result = evaluateLppExpression(expression, {});

    if (isObject(result) && result.__lpp === 'Extension') {
      extension = result;
      break;
    }
  }

  if (!extension) {
    return {
      blocks: [],
      recognized: false
    };
  }

  const blocks = [];

  for (const item of extension.blocks) {
    if (item.__lpp === 'Button') {
      const id = item.args && item.args.length
        ? item.args[0]
        : null;

      blocks.push({
        opcode: typeof id === 'string' ? id : null,
        blockType: 'button',
        text: null,
        arguments: {},
        fieldStatus: {
          dynamic: ['text'],
          functions: [],
          unknown: []
        }
      });

      continue;
    }

    if (item.__lpp !== 'Category') continue;

    blocks.push({
      opcode: null,
      blockType: 'label',
      text: null,
      arguments: {},
      category: null,
      fieldStatus: {
        dynamic: ['text'],
        functions: [],
        unknown: []
      }
    });

    for (const entry of item.entries) {
      const typeName = entry.block.type || '';

      let blockType = null;

      if (/Reporter/i.test(typeName)) blockType = 'reporter';
      else if (/Command/i.test(typeName)) blockType = 'command';
      else if (/Boolean/i.test(typeName)) blockType = 'Boolean';
      else if (/Hat/i.test(typeName)) blockType = 'hat';
      else if (/Loop/i.test(typeName)) blockType = 'loop';

      blocks.push({
        opcode: entry.opcode,
        blockType,
        text: '',
        arguments: {},
        fieldStatus: {
          dynamic: [],
          functions: [],
          unknown: blockType ? [] : ['blockType']
        }
      });
    }
  }

  return {
    blocks,
    recognized: blocks.length > 0
  };
}

function inspectFields(block) {
  const status = {
    dynamic: [],
    functions: [],
    unknown: [],
    spreads: []
  };

  function walk(value, prefix) {
    if (isMarker(value)) {
      if ('$dynamic' in value) status.dynamic.push(prefix);
      else if ('$function' in value) status.functions.push(prefix);
      else status.unknown.push(prefix);
      return;
    }

    if (Array.isArray(value)) {
      value.forEach((item, index) => walk(item, `${prefix}[${index}]`));
      return;
    }

    if (isObject(value)) {
      if (value.$spread) status.spreads.push(prefix);

      for (const [key, child] of Object.entries(value)) {
        if (key === '$spread') continue;
        walk(child, prefix ? `${prefix}.${key}` : key);
      }
    }
  }

  walk(block, '');

  status.dynamic = [...new Set(status.dynamic)];
  status.functions = [...new Set(status.functions)];
  status.unknown = [...new Set(status.unknown)];
  status.spreads = [...new Set(status.spreads)];

  return status;
}

function cleanFunctions(value) {
  if (Array.isArray(value)) {
    return value.map(cleanFunctions);
  }

  if (!isObject(value)) return value;

  if ('$function' in value) return null;

  const result = {};

  for (const [key, child] of Object.entries(value)) {
    if (key === '$function') continue;
    result[key] = cleanFunctions(child);
  }

  return result;
}

function scanFile(filePath, repositoryPath) {
  const relativePath = path.relative(repositoryPath, filePath)
    .split(path.sep)
    .join('/');

  const result = {
    file: relativePath,
    status: 'no_static_getInfo',
    blockCount: 0,
    dynamicFieldCount: 0,
    functionFieldCount: 0,
    unknownFieldCount: 0,
    omittedDynamicBlockCount: 0,
    errors: []
  };

  try {
    const source = fs.readFileSync(filePath, 'utf8');
    const ast = parseSource(source, relativePath);
    const messages = extractMessages(ast);
    const context = { messages };
    const env = buildTopLevelSymbols(ast, context);

    const infoObjects = getInfoObjects(ast, env, context);
    let info = infoObjects[0] || null;

    let rawBlocks = null;

    if (info) {
      rawBlocks = findProperty(info, 'blocks');
    }

    // LPP：blocks: this.extension.export()
    if (
      !Array.isArray(rawBlocks) &&
      /FurryR[\\/]lpp\.js$/i.test(filePath)
    ) {
      const lpp = extractLppBlocks(ast);

      if (lpp.recognized) {
        rawBlocks = lpp.blocks;
        result.lppStaticExtraction = true;
      }
    }

    if (!info && !rawBlocks) {
      result.status = 'no_static_getInfo';
      return { result, blocks: [] };
    }

    if (!Array.isArray(rawBlocks)) {
      result.status = 'dynamic_blocks';
      result.omittedDynamicBlockCount = 1;
      return { result, blocks: [] };
    }

    const extension = getExtensionInfo(info || {}, relativePath);
    const blocks = [];

    for (let i = 0; i < rawBlocks.length; i++) {
      const rawBlock = rawBlocks[i];

      // 分类分隔符不是积木元数据。
      if (typeof rawBlock === 'string') continue;

      if (!isObject(rawBlock)) {
        result.omittedDynamicBlockCount++;
        continue;
      }

      const fieldStatus = inspectFields(rawBlock);
      const normalized = normalizeBlock(
        cleanFunctions(rawBlock),
        extension,
        relativePath,
        i
      );

      normalized.fieldStatus = fieldStatus;

      result.dynamicFieldCount += fieldStatus.dynamic.length;
      result.functionFieldCount += fieldStatus.functions.length;
      result.unknownFieldCount += fieldStatus.unknown.length;

      blocks.push(normalized);
    }

    result.blockCount = blocks.length;

    if (result.unknownFieldCount > 0) {
      result.status = 'unknown_fields';
    } else if (
      result.dynamicFieldCount > 0 ||
      result.omittedDynamicBlockCount > 0
    ) {
      result.status = 'dynamic_fields';
    } else {
      result.status = 'success';
    }

    return { result, blocks };

  } catch (error) {
    result.status = 'error';
    result.errors.push({
      message: error.message,
      name: error.name
    });

    return { result, blocks: [] };
  }
}

function readSources() {
  if (!fs.existsSync(SOURCES_FILE)) {
    throw new Error('找不到 sources.txt');
  }

  return fs.readFileSync(SOURCES_FILE, 'utf8')
    .split(/\r?\n/)
    .map(line => line.trim())
    .filter(line => line && !line.startsWith('#'));
}

function cloneRepository(url, destination) {
  execFileSync(
    'git',
    ['clone', '--depth', '1', url, destination],
    { stdio: 'inherit' }
  );
}

function findJavaScriptFiles(directory) {
  const results = [];

  const ignoredDirectories = new Set([
    '.git',
    'node_modules',
    'dist',
    'build',
    'coverage',
    'test',
    'tests',
    '__tests__'
  ]);

  function walk(current) {
    if (!fs.existsSync(current)) return;

    for (const entry of fs.readdirSync(current, { withFileTypes: true })) {
      const fullPath = path.join(current, entry.name);

      if (entry.isDirectory()) {
        if (!ignoredDirectories.has(entry.name)) walk(fullPath);
        continue;
      }

      if (!entry.isFile()) continue;
      if (!/\.(js|cjs|mjs)$/.test(entry.name)) continue;

      results.push(fullPath);
    }
  }

  walk(directory);
  return results;
}

function buildDuplicateReport(blocks) {
  const globalMap = new Map();
  const namespacedMap = new Map();

  for (const block of blocks) {
    if (typeof block.opcode !== 'string' || !block.opcode) continue;

    const globalKey = block.opcode;
    const namespaceKey =
      `${block.extensionId || 'unknown'}::${block.opcode}`;

    if (!globalMap.has(globalKey)) globalMap.set(globalKey, []);
    if (!namespacedMap.has(namespaceKey)) namespacedMap.set(namespaceKey, []);

    globalMap.get(globalKey).push(block);
    namespacedMap.get(namespaceKey).push(block);
  }

  function duplicates(map) {
    const result = [];

    for (const [key, values] of map.entries()) {
      if (values.length < 2) continue;

      result.push({
        key,
        count: values.length,
        files: [...new Set(values.map(v => v.sourceFile))]
      });
    }

    return result;
  }

  return {
    global: duplicates(globalMap),
    namespaced: duplicates(namespacedMap)
  };
}

function countMissingFields(blocks) {
  const fields = [
    'opcode',
    'text',
    'text_en',
    'blockType',
    'category',
    'category_en',
    'arguments'
  ];

  const result = {};

  for (const field of fields) {
    result[field] = blocks.filter(block =>
      block[field] === null || block[field] === undefined
    ).length;
  }

  return result;
}

function main() {
  const sources = readSources();

  const tempRoot = fs.mkdtempSync(
    path.join(os.tmpdir(), 'ccw-extension-db-')
  );

  const allBlocks = [];
  const fileReports = [];
  const repositoryReports = [];

  try {
    for (let sourceIndex = 0; sourceIndex < sources.length; sourceIndex++) {
      const sourceUrl = sources[sourceIndex];
      const repositoryPath = path.join(
        tempRoot,
        `repository-${sourceIndex}`
      );

      console.log(`\n[${sourceIndex + 1}/${sources.length}] ${sourceUrl}`);

      try {
        cloneRepository(sourceUrl, repositoryPath);

        const extensionDirectory = path.join(
          repositoryPath,
          'extensions'
        );

        const scanDirectory = fs.existsSync(extensionDirectory)
          ? extensionDirectory
          : repositoryPath;

        const files = findJavaScriptFiles(scanDirectory);
        const repositoryBlocks = [];
        const repositoryFileReports = [];

        for (const file of files) {
          const scanned = scanFile(file, repositoryPath);

          repositoryFileReports.push(scanned.result);
          repositoryBlocks.push(...scanned.blocks);
        }

        allBlocks.push(...repositoryBlocks);
        fileReports.push(...repositoryFileReports);

        repositoryReports.push({
          source: sourceUrl,
          fileCount: files.length,
          blockCount: repositoryBlocks.length
        });

      } catch (error) {
        repositoryReports.push({
          source: sourceUrl,
          error: error.message
        });
      }
    }

    const statusCounts = {};
    for (const report of fileReports) {
      statusCounts[report.status] =
        (statusCounts[report.status] || 0) + 1;
    }

    const successfulFiles = statusCounts.success || 0;
    const dynamicFiles = statusCounts.dynamic_blocks || 0;
    const dynamicFieldFiles = statusCounts.dynamic_fields || 0;
    const unknownFiles = statusCounts.unknown_fields || 0;
    const errorFiles = statusCounts.error || 0;
    const unrecognizedFiles = statusCounts.no_static_getInfo || 0;

    const dynamicFieldCount = fileReports.reduce(
      (sum, item) => sum + item.dynamicFieldCount,
      0
    );

    const functionFieldCount = fileReports.reduce(
      (sum, item) => sum + item.functionFieldCount,
      0
    );

    const unknownFieldCount = fileReports.reduce(
      (sum, item) => sum + item.unknownFieldCount,
      0
    );

    const omittedDynamicBlockCount = fileReports.reduce(
      (sum, item) => sum + item.omittedDynamicBlockCount,
      0
    );

    const database = {
      schemaVersion: SCHEMA_VERSION,
      extractorVersion: EXTRACTOR_VERSION,
      generatedAt: new Date().toISOString(),
      sourceCount: sources.length,
      blockCount: allBlocks.length,
      blocks: allBlocks,
      duplicateOpcodes: buildDuplicateReport(allBlocks),
      quality: {
        missingFields: countMissingFields(allBlocks),
        dynamicFieldCount,
        functionFieldCount,
        unknownFieldCount,
        omittedDynamicBlockCount
      }
    };

    const extractionReport = {
      schemaVersion: SCHEMA_VERSION,
      extractorVersion: EXTRACTOR_VERSION,
      generatedAt: new Date().toISOString(),

      sourceCount: sources.length,
      fileCount: fileReports.length,
      blockCount: allBlocks.length,

      successfulFiles,
      dynamicFiles,
      dynamicFieldFiles,
      unknownFiles,
      unrecognizedFiles,
      errorFiles,

      dynamicFieldCount,
      functionFieldCount,
      unknownFieldCount,
      omittedDynamicBlockCount,

      statusCounts,
      repositories: repositoryReports,
      files: fileReports
    };

    const versionReport = {
      generatedAt: new Date().toISOString(),
      extractorVersion: EXTRACTOR_VERSION,
      schemaVersion: SCHEMA_VERSION,
      sources
    };

    fs.writeFileSync(
      OUTPUT_DATABASE,
      JSON.stringify(database, null, 2) + '\n'
    );

    fs.writeFileSync(
      OUTPUT_REPORT,
      JSON.stringify(extractionReport, null, 2) + '\n'
    );

    fs.writeFileSync(
      OUTPUT_VERSION,
      JSON.stringify(versionReport, null, 2) + '\n'
    );

    console.log('\n========== Extraction Summary ==========');
    console.log(`Files: ${fileReports.length}`);
    console.log(`Blocks: ${allBlocks.length}`);
    console.log(`Successful: ${successfulFiles}`);
    console.log(`Dynamic blocks: ${dynamicFiles}`);
    console.log(`Dynamic fields: ${dynamicFieldFiles}`);
    console.log(`Unknown fields: ${unknownFiles}`);
    console.log(`Unrecognized: ${unrecognizedFiles}`);
    console.log(`Errors: ${errorFiles}`);
    console.log(`Dynamic field count: ${dynamicFieldCount}`);
    console.log(`Function field count: ${functionFieldCount}`);
    console.log(`Unknown field count: ${unknownFieldCount}`);
    console.log(`Omitted dynamic blocks: ${omittedDynamicBlockCount}`);
    console.log('========================================');

  } finally {
    fs.rmSync(tempRoot, { recursive: true, force: true });
  }
}

main();
