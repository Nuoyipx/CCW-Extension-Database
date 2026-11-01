import json
import re
import subprocess
import tempfile
import shutil
from pathlib import Path
from datetime import datetime, timezone

DATABASE_FILE = "blocks_database.json"
REPORT_FILE = "extraction_report.json"
VERSION_FILE = "version_report.json"

EXCLUDED_DIRS = {
    ".git", "node_modules", "__pycache__",
    "dist", "build", ".github"
}


# --------------------------------------------------
# JavaScript tokenizer
# --------------------------------------------------

TOKEN_PATTERN = re.compile(
    r"""
    (?P<space>\s+)
    |(?P<linecomment>//[^\n]*)
    |(?P<blockcomment>/\*[\s\S]*?\*/)
    |(?P<string>'(?:\\.|[^'\\])*'|"(?:\\.|[^"\\])*")
    |(?P<template>`(?:\\.|[^`\\])*`)
    |(?P<number>-?\d+(?:\.\d+)?)
    |(?P<identifier>[A-Za-z_$][A-Za-z0-9_$]*)
    |(?P<operator>=>|\.\.\.|\?\?|&&|\|\||===|!==|==|!=|<=|>=)
    |(?P<punctuation>[{}\[\]():,.;])
    |(?P<other>.)
    """,
    re.VERBOSE
)


def tokenize(source):
    tokens = []

    for match in TOKEN_PATTERN.finditer(source):
        kind = match.lastgroup
        value = match.group()

        if kind in ("space", "linecomment", "blockcomment"):
            continue

        tokens.append(value)

    return tokens


# --------------------------------------------------
# JavaScript literal parser
# --------------------------------------------------

class JSParser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def peek(self):
        if self.pos >= len(self.tokens):
            return None
        return self.tokens[self.pos]

    def take(self):
        value = self.peek()
        if value is not None:
            self.pos += 1
        return value

    def skip_expression(self):
        depth = 0

        while self.pos < len(self.tokens):
            token = self.peek()

            if depth == 0 and token in (",", "}", "]"):
                return

            if token in ("(", "[", "{"):
                depth += 1
            elif token in (")", "]", "}"):
                if depth == 0:
                    return
                depth -= 1

            self.pos += 1

    def parse_string(self, token):
        if token.startswith("`"):
            return token[1:-1]

        try:
            return json.loads(token.replace("'", '"'))
        except Exception:
            return token[1:-1]

    def parse_value(self):
        token = self.peek()

        if token is None:
            return None

        if token == "{":
            return self.parse_object()

        if token == "[":
            return self.parse_array()

        if token.startswith(("'", '"', "`")):
            self.take()
            return self.parse_string(token)

        if token in ("true", "false", "null", "undefined"):
            self.take()
            return {
                "true": True,
                "false": False,
                "null": None,
                "undefined": None
            }[token]

        if re.fullmatch(r"-?\d+(?:\.\d+)?", token):
            self.take()
            return float(token) if "." in token else int(token)

        if token == "-" and self.pos + 1 < len(self.tokens):
            if re.fullmatch(r"\d+(?:\.\d+)?", self.tokens[self.pos + 1]):
                self.take()
                number = self.take()
                return -float(number) if "." in number else -int(number)

        # Constants and expressions are not evaluated.
        self.skip_expression()
        return None

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

            key = self.take()

            if key.startswith(("'", '"', "`")):
                key = self.parse_string(key)

            if self.peek() == ":":
                self.take()
                result[str(key)] = self.parse_value()

            else:
                # Shorthand properties and methods are not evaluated.
                self.skip_expression()

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

            result.append(self.parse_value())

            if self.peek() == ",":
                self.take()

        return result


# --------------------------------------------------
# Find getInfo() metadata
# --------------------------------------------------

def extract_getinfo(source):
    tokens = tokenize(source)

    for i in range(len(tokens) - 2):
        if tokens[i] != "getInfo":
            continue

        if tokens[i + 1] != "(":
            continue

        # Find the method body.
        j = i + 2
        paren_depth = 1

        while j < len(tokens) and paren_depth:
            if tokens[j] == "(":
                paren_depth += 1
            elif tokens[j] == ")":
                paren_depth -= 1
            j += 1

        if j >= len(tokens) or tokens[j] != "{":
            continue

        body_start = j
        depth = 0
        body_end = None

        for k in range(body_start, len(tokens)):
            if tokens[k] == "{":
                depth += 1
            elif tokens[k] == "}":
                depth -= 1
                if depth == 0:
                    body_end = k
                    break

        if body_end is None:
            continue

        body = tokens[body_start + 1:body_end]

        for r in range(len(body) - 1):
            if body[r] == "return" and body[r + 1] == "{":
                parser = JSParser(body[r + 1:])
                try:
                    info = parser.parse_value()
                    if isinstance(info, dict):
                        return info
                except Exception:
                    pass

    return None


# --------------------------------------------------
# Normalize block information
# --------------------------------------------------

def normalize_block(block, extension_id, extension_name, file_path):
    if not isinstance(block, dict):
        return None

    return {
        "extensionId": extension_id,
        "extensionName": extension_name,
        "opcode": block.get("opcode"),
        "text": block.get("text"),
        "blockType": block.get("blockType"),
        "arguments": block.get("arguments", {}),
        "branchCount": block.get("branchCount"),
        "terminal": block.get("terminal"),
        "filter": block.get("filter"),
        "sourceFile": file_path
    }


# --------------------------------------------------
# Scan one JavaScript file
# --------------------------------------------------

def scan_file(file_path, source_root):
    relative_path = str(file_path.relative_to(source_root))

    result = {
        "file": relative_path,
        "status": "unknown",
        "blocksFound": 0,
        "message": ""
    }

    try:
        source = file_path.read_text(encoding="utf-8", errors="replace")
        info = extract_getinfo(source)

        if not info:
            result["status"] = "no_static_getInfo"
            result["message"] = "No statically readable getInfo() metadata."
            return [], result

        extension_id = info.get("id")
        extension_name = info.get("name")
        blocks = info.get("blocks", [])

        if not isinstance(blocks, list):
            result["status"] = "dynamic_blocks"
            result["message"] = "The blocks property is not a static array."
            return [], result

        extracted = []

        for block in blocks:
            normalized = normalize_block(
                block,
                extension_id,
                extension_name,
                relative_path
            )

            if normalized:
                extracted.append(normalized)

        result["status"] = "success"
        result["blocksFound"] = len(extracted)

        return extracted, result

    except Exception as error:
        result["status"] = "error"
        result["message"] = str(error)
        return [], result


# --------------------------------------------------
# Clone source repositories
# --------------------------------------------------

def read_sources():
    path = Path("sources.txt")

    if not path.exists():
        raise FileNotFoundError("sources.txt was not found.")

    sources = []

    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()

        if line and not line.startswith("#"):
            sources.append(line)

    return sources


def clone_repository(url, destination):
    subprocess.run(
        ["git", "clone", "--depth", "1", url, str(destination)],
        check=True,
        capture_output=True,
        text=True
    )


# --------------------------------------------------
# Main extraction
# --------------------------------------------------

def main():
    print("Starting CCW extension extraction...")

    all_blocks = []
    all_reports = []
    version_reports = []

    sources = read_sources()

    if not sources:
        raise RuntimeError("No source repositories found in sources.txt.")

    with tempfile.TemporaryDirectory() as temporary:
        temporary_path = Path(temporary)

        for index, url in enumerate(sources):
            print(f"Cloning source {index + 1}: {url}")

            repository_path = temporary_path / f"source_{index}"

            try:
                clone_repository(url, repository_path)

            except Exception as error:
                all_reports.append({
                    "repository": url,
                    "status": "clone_error",
                    "message": str(error)
                })
                continue

            commit = subprocess.run(
                ["git", "-C", str(repository_path), "rev-parse", "HEAD"],
                capture_output=True,
                text=True
            ).stdout.strip()

            version_reports.append({
                "repository": url,
                "commit": commit,
                "versionStatus": "unknown",
                "note": "Only the default branch was scanned."
            })

            for file_path in repository_path.rglob("*.js"):
                if any(part in EXCLUDED_DIRS for part in file_path.parts):
                    continue

                blocks, report = scan_file(file_path, repository_path)

                report["repository"] = url
                all_reports.append(report)
                all_blocks.extend(blocks)

    # Detect duplicate opcodes.
    opcode_map = {}

    for block in all_blocks:
        opcode = block.get("opcode")

        if opcode:
            opcode_map.setdefault(opcode, []).append(block["sourceFile"])

    duplicates = {
        opcode: files
        for opcode, files in opcode_map.items()
        if len(files) > 1
    }

    database = {
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "sourceCount": len(sources),
        "blockCount": len(all_blocks),
        "blocks": all_blocks,
        "duplicateOpcodes": duplicates
    }

    report_data = {
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "fileCount": len(all_reports),
        "successfulFiles": sum(
            1 for item in all_reports
            if item.get("status") == "success"
        ),
        "files": all_reports
    }

    Path(DATABASE_FILE).write_text(
        json.dumps(database, ensure_ascii=False, indent=2),
        encoding="utf-8"
    )

    Path(REPORT_FILE).write_text(
        json.dumps(report_data, ensure_ascii=False, indent=2),
        encoding="utf-8"
    )

    Path(VERSION_FILE).write_text(
        json.dumps(version_reports, ensure_ascii=False, indent=2),
        encoding="utf-8"
    )

    print("Extraction finished.")
    print(f"Blocks extracted: {len(all_blocks)}")
    print(f"Files scanned: {len(all_reports)}")
    print(f"Duplicate opcodes: {len(duplicates)}")


if __name__ == "__main__":
    main()
