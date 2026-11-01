
import ast
import json
import re
import subprocess
import tempfile
from pathlib import Path
from datetime import datetime, timezone


DATABASE_FILE = "blocks_database.json"
REPORT_FILE = "extraction_report.json"
VERSION_FILE = "version_report.json"

EXCLUDED_DIRS = {
    ".git",
    "node_modules",
    "__pycache__",
    "dist",
    "build",
    "assets",
    "coverage",
}

EXCLUDED_FILES = {
    "webpack.config.js",
    "vite.config.js",
    ".eslintrc.js",
    "babel.config.js",
    "jest.config.js",
}

TOKEN_RE = re.compile(
    r"""
    (?P<space>\s+)
    |(?P<line_comment>//[^\n]*)
    |(?P<block_comment>/\*[\s\S]*?\*/)
    |(?P<string>'(?:\\.|[^'\\])*'|"(?:\\.|[^"\\])*")
    |(?P<template>`(?:\\.|[^`\\])*`)
    |(?P<number>\d+(?:\.\d+)?)
    |(?P<identifier>[A-Za-z_$][A-Za-z0-9_$]*)
    |(?P<operator>=>|\.\.\.|\?\?=|\?\?|\?\.|&&|\|\||===|!==|==|!=|<=|>=|\+=)
    |(?P<punctuation>[{}\[\]():,;.=+\-*/!?<>])
    |(?P<other>.)
    """,
    re.VERBOSE,
)


def now():
    return datetime.now(timezone.utc).isoformat()


def tokenize(source):
    tokens = []

    for match in TOKEN_RE.finditer(source):
        kind = match.lastgroup

        if kind in ("space", "line_comment", "block_comment"):
            continue

        tokens.append(match.group())

    return tokens


def decode_string(token):
    if token.startswith("`"):
        return token[1:-1]

    body = token[1:-1]

    replacements = {
        r"\n": "\n",
        r"\r": "\r",
        r"\t": "\t",
        r"\\": "\\",
        r"\'": "'",
        r'\"': '"',
    }

    for old, new in replacements.items():
        body = body.replace(old, new)

    body = re.sub(
        r"\\u([0-9a-fA-F]{4})",
        lambda m: chr(int(m.group(1), 16)),
        body,
    )

    body = re.sub(
        r"\\x([0-9a-fA-F]{2})",
        lambda m: chr(int(m.group(1), 16)),
        body,
    )

    return body


class JSParser:
    def __init__(self, tokens, symbols=None):
        self.tokens = tokens
        self.pos = 0
        self.symbols = symbols or {}

    def peek(self):
        if self.pos >= len(self.tokens):
            return None
        return self.tokens[self.pos]

    def take(self):
        value = self.peek()

        if value is not None:
            self.pos += 1

        return value

    def collect_expression(self, stops):
        start = self.pos

        paren = 0
        bracket = 0
        brace = 0

        while self.pos < len(self.tokens):
            token = self.peek()

            if paren == 0 and bracket == 0 and brace == 0:
                if token in stops:
                    break

            if token == "(":
                paren += 1
            elif token == ")":
                if paren == 0:
                    break
                paren -= 1

            elif token == "[":
                bracket += 1
            elif token == "]":
                if bracket == 0:
                    break
                bracket -= 1

            elif token == "{":
                brace += 1
            elif token == "}":
                if brace == 0:
                    break
                brace -= 1

            self.pos += 1

        return self.tokens[start:self.pos]

    def parse_expression(self, stops):
        token = self.peek()

        if token is None:
            return None

        if token == "{":
            return self.parse_object()

        if token == "[":
            return self.parse_array()

        expression = self.collect_expression(stops)

        if not expression:
            return None

        if len(expression) == 1:
            value = expression[0]

            if value.startswith(("'", '"', "`")):
                return decode_string(value)

            if value == "true":
                return True

            if value == "false":
                return False

            if value in ("null", "undefined"):
                return None

            if re.fullmatch(r"\d+(?:\.\d+)?", value):
                return float(value) if "." in value else int(value)

            if value in self.symbols:
                return self.symbols[value]

        return {
            "$expression": " ".join(expression)
        }

    def parse_object(self):
        result = {}

        self.take()  # {

        while self.pos < len(self.tokens):
            token = self.peek()

            if token == "}":
                self.take()
                break

            if token == ",":
                self.take()
                continue

            if token is None:
                break

            if token == "...":
                self.collect_expression({",", "}"})
                continue

            key = self.take()

            if key.startswith(("'", '"', "`")):
                key = decode_string(key)

            if key == "[":
                self.collect_expression({"]"})
                if self.peek() == "]":
                    self.take()

                self.collect_expression({",", "}"})
                continue

            if self.peek() == ":":
                self.take()

                value = self.parse_expression({",", "}"})
                result[str(key)] = value

            else:
                if key in self.symbols:
                    result[str(key)] = self.symbols[key]

                else:
                    result[str(key)] = {
                        "$expression": str(key)
                    }

                # Skip method bodies and other shorthand syntax.
                if self.peek() == "(":
                    self.collect_expression({",", "}"})

            if self.peek() == ",":
                self.take()

        return result

    def parse_array(self):
        result = []

        self.take()  # [

        while self.pos < len(self.tokens):
            token = self.peek()

            if token == "]":
                self.take()
                break

            if token == ",":
                self.take()
                continue

            if token is None:
                break

            if token == "...":
                self.take()

                expression = self.parse_expression({",", "]"})

                result.append({
                    "$spread": expression
                })

            else:
                result.append(
                    self.parse_expression({",", "]"})
                )

            if self.peek() == ",":
                self.take()

        return result


def matching_brace(tokens, start):
    if start >= len(tokens) or tokens[start] != "{":
        return None

    depth = 0

    for index in range(start, len(tokens)):
        if tokens[index] == "{":
            depth += 1

        elif tokens[index] == "}":
            depth -= 1

            if depth == 0:
                return index

    return None


def find_getinfo_bodies(tokens):
    bodies = []

    for i, token in enumerate(tokens):
        if token != "getInfo":
            continue

        if i > 0 and tokens[i - 1] in (".", "?."):
            continue

        j = i + 1

        if j >= len(tokens) or tokens[j] != "(":
            continue

        # Find the end of the parameter list.
        depth = 0
        end_params = None

        for k in range(j, len(tokens)):
            if tokens[k] == "(":
                depth += 1

            elif tokens[k] == ")":
                depth -= 1

                if depth == 0:
                    end_params = k
                    break

        if end_params is None:
            continue

        # Find the method or arrow-function body.
        body_start = None

        for k in range(end_params + 1, min(end_params + 12, len(tokens))):
            if tokens[k] == "{":
                body_start = k
                break

            if tokens[k] == ";":
                break

        if body_start is None:
            continue

        body_end = matching_brace(tokens, body_start)

        if body_end is None:
            continue

        bodies.append(
            tokens[body_start + 1:body_end]
        )

    return bodies


def collect_local_symbols(body):
    symbols = {}

    for i, token in enumerate(body):
        if token not in ("const", "let", "var"):
            continue

        if i + 2 >= len(body):
            continue

        name = body[i + 1]

        if not re.fullmatch(r"[A-Za-z_$][A-Za-z0-9_$]*", name):
            continue

        if body[i + 2] != "=":
            continue

        parser = JSParser(
            body[i + 3:],
            symbols,
        )

        try:
            value = parser.parse_expression({";", ","})

            if isinstance(value, (dict, list, str, int, float, bool)):
                symbols[name] = value

        except Exception:
            continue

    return symbols


def extract_info_from_body(body):
    symbols = collect_local_symbols(body)

    for i, token in enumerate(body):
        if token != "return":
            continue

        if i + 1 >= len(body):
            continue

        if body[i + 1] != "{":
            continue

        parser = JSParser(
            body[i + 1:],
            symbols,
        )

        try:
            info = parser.parse_expression({";"})

            if isinstance(info, dict):
                return info

        except Exception:
            continue

    return None


def extract_getinfo(source):
    tokens = tokenize(source)
    bodies = find_getinfo_bodies(tokens)

    for body in bodies:
        info = extract_info_from_body(body)

        if info is not None:
            return info

    return None


def contains_expression(value):
    if isinstance(value, dict):
        if "$expression" in value or "$spread" in value:
            return True

        return any(
            contains_expression(v)
            for v in value.values()
        )

    if isinstance(value, list):
        return any(
            contains_expression(v)
            for v in value
        )

    return False


def normalize_block(block, info, source_file, repository):
    if not isinstance(block, dict):
        return None

    if not any(
        key in block
        for key in ("opcode", "blockType", "text")
    ):
        return None

    return {
        "extensionId": info.get("id"),
        "extensionName": info.get("name"),
        "opcode": block.get("opcode"),
        "text": block.get("text"),
        "blockType": block.get("blockType"),
        "arguments": block.get("arguments", {}),
        "branchCount": block.get("branchCount"),
        "terminal": block.get("terminal"),
        "filter": block.get("filter"),
        "sourceFile": source_file,
        "repository": repository,
    }


def scan_file(file_path, repository_root, repository_url):
    relative_path = str(
        file_path.relative_to(repository_root)
    )

    report = {
        "file": relative_path,
        "status": "unknown",
        "blocksFound": 0,
        "message": "",
    }

    try:
        source = file_path.read_text(
            encoding="utf-8",
            errors="replace",
        )

        info = extract_getinfo(source)

        if not info:
            report["status"] = "no_static_getInfo"
            report["message"] = (
                "No statically readable getInfo() return object."
            )

            return [], report

        blocks = info.get("blocks")

        if isinstance(blocks, dict) and "$expression" in blocks:
            report["status"] = "dynamic_blocks"
            report["message"] = (
                "The blocks property is generated by an expression."
            )

            return [], report

        if not isinstance(blocks, list):
            report["status"] = "dynamic_blocks"
            report["message"] = (
                "The blocks property is not a static array."
            )

            return [], report

        extracted = []

        for block in blocks:
            if isinstance(block, dict) and "$spread" in block:
                continue

            normalized = normalize_block(
                block,
                info,
                relative_path,
                repository_url,
            )

            if normalized:
                extracted.append(normalized)

        report["blocksFound"] = len(extracted)

        if any(
            contains_expression(block)
            for block in blocks
        ):
            report["status"] = "partial"
            report["message"] = (
                "Some block entries contain unresolved expressions."
            )

        else:
            report["status"] = "success"

        return extracted, report

    except Exception as error:
        report["status"] = "error"
        report["message"] = str(error)

        return [], report


def read_sources():
    path = Path("sources.txt")

    if not path.exists():
        raise FileNotFoundError(
            "sources.txt was not found."
        )

    sources = []

    for line in path.read_text(
        encoding="utf-8"
    ).splitlines():

        line = line.strip()

        if line and not line.startswith("#"):
            sources.append(line)

    return sources


def clone_repository(url, destination):
    subprocess.run(
        [
            "git",
            "clone",
            "--depth",
            "1",
            url,
            str(destination),
        ],
        check=True,
        capture_output=True,
        text=True,
    )


def get_commit(repository_path):
    result = subprocess.run(
        [
            "git",
            "-C",
            str(repository_path),
            "rev-parse",
            "HEAD",
        ],
        capture_output=True,
        text=True,
    )

    return result.stdout.strip()


def should_scan(path, extensions_root):
    if not path.is_file():
        return False

    if path.suffix.lower() != ".js":
        return False

    if path.name in EXCLUDED_FILES:
        return False

    relative = path.relative_to(extensions_root)

    if any(
        part in EXCLUDED_DIRS
        for part in relative.parts
    ):
        return False

    return True


def main():
    print("Starting CCW extension extraction...")

    sources = read_sources()

    if not sources:
        raise RuntimeError(
            "No source repositories found in sources.txt."
        )

    all_blocks = []
    all_reports = []
    version_reports = []

    with tempfile.TemporaryDirectory() as temporary:
        temporary_path = Path(temporary)

        for index, url in enumerate(sources):
            print(f"Cloning source {index + 1}: {url}")

            repository_path = (
                temporary_path / f"source_{index}"
            )

            try:
                clone_repository(
                    url,
                    repository_path,
                )

            except Exception as error:
                all_reports.append({
                    "repository": url,
                    "status": "clone_error",
                    "blocksFound": 0,
                    "message": str(error),
                })

                continue

            commit = get_commit(repository_path)

            version_reports.append({
                "repository": url,
                "commit": commit,
                "versionStatus": "unknown",
                "note": (
                    "Only the default branch was scanned. "
                    "Other branches and historical commits "
                    "have not been scanned."
                ),
            })

            extensions_root = repository_path / "extensions"

            if not extensions_root.is_dir():
                all_reports.append({
                    "repository": url,
                    "status": "missing_extensions_directory",
                    "blocksFound": 0,
                    "message": (
                        "The repository has no extensions/ directory."
                    ),
                })

                continue

            files = sorted(
                extensions_root.rglob("*.js")
            )

            for file_path in files:
                if not should_scan(
                    file_path,
                    extensions_root,
                ):
                    continue

                blocks, report = scan_file(
                    file_path,
                    repository_path,
                    url,
                )

                report["repository"] = url

                all_reports.append(report)
                all_blocks.extend(blocks)

                print(
                    f"{report['status']}: "
                    f"{report['file']} "
                    f"({report['blocksFound']} blocks)"
                )

    # Duplicate opcode report.
    opcode_map = {}

    for block in all_blocks:
        opcode = block.get("opcode")

        if isinstance(opcode, str) and opcode:
            opcode_map.setdefault(
                opcode,
                [],
            ).append({
                "sourceFile": block["sourceFile"],
                "repository": block["repository"],
            })

    duplicates = {
        opcode: locations
        for opcode, locations in opcode_map.items()
        if len(locations) > 1
    }

    status_counts = {}

    for report in all_reports:
        status = report.get("status", "unknown")

        status_counts[status] = (
            status_counts.get(status, 0) + 1
        )

    generated_at = now()

    database = {
        "generatedAt": generated_at,
        "sourceCount": len(sources),
        "fileCount": len(all_reports),
        "blockCount": len(all_blocks),
        "blocks": all_blocks,
        "duplicateOpcodes": duplicates,
    }

    extraction_report = {
        "generatedAt": generated_at,
        "fileCount": len(all_reports),
        "successfulFiles": status_counts.get("success", 0),
        "partialFiles": status_counts.get("partial", 0),
        "dynamicFiles": status_counts.get("dynamic_blocks", 0),
        "unrecognizedFiles": status_counts.get(
            "no_static_getInfo", 0
        ),
        "errorFiles": status_counts.get("error", 0),
        "statusCounts": status_counts,
        "files": all_reports,
    }

    Path(DATABASE_FILE).write_text(
        json.dumps(
            database,
            ensure_ascii=False,
            indent=2,
        ),
        encoding="utf-8",
    )

    Path(REPORT_FILE).write_text(
        json.dumps(
            extraction_report,
            ensure_ascii=False,
            indent=2,
        ),
        encoding="utf-8",
    )

    Path(VERSION_FILE).write_text(
        json.dumps(
            version_reports,
            ensure_ascii=False,
            indent=2,
        ),
        encoding="utf-8",
    )

    print("")
    print("Extraction finished.")
    print(f"Repositories: {len(sources)}")
    print(f"Files scanned: {len(all_reports)}")
    print(f"Blocks extracted: {len(all_blocks)}")
    print(f"Successful files: {status_counts.get('success', 0)}")
    print(f"Partial files: {status_counts.get('partial', 0)}")
    print(f"Dynamic files: {status_counts.get('dynamic_blocks', 0)}")
    print(f"Unrecognized files: {status_counts.get('no_static_getInfo', 0)}")
    print(f"Errors: {status_counts.get('error', 0)}")
    print(f"Duplicate opcodes: {len(duplicates)}")


if __name__ == "__main__":
    main()
