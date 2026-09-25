"""Check the repository's GitHub-safe Markdown math delimiters.

This is a formatting gate, not a Lean proof or a full TeX renderer. Inline
math uses dollar/backtick delimiters; displays use fenced ``math`` blocks.
Ordinary code fences and inline code are excluded from prose checks.
Optional paths restrict the check to specific Markdown files/directories.
"""

from pathlib import Path
import argparse
import json
import re


def inspect(path):
    text = path.read_text(encoding="utf-8")
    errors, counts = [], {"inline": 0, "display": 0}
    fence = None
    inline_open = False
    for number, line in enumerate(text.splitlines(), 1):
        marker = re.match(r"^\s{0,3}(`{3,}|~{3,})(.*)$", line)
        if fence:
            if marker and marker[1][0] == fence[0] and len(marker[1]) >= fence[1] and not marker[2].strip():
                fence = None
            continue
        if marker:
            if inline_open:
                errors.append({"line": number, "issue": "inline math crosses a code fence"})
            fence = (marker[1][0], len(marker[1]), number)
            if marker[2].strip() == "math":
                counts["display"] += 1
            continue

        is_table = line.lstrip().startswith("|")
        pos = 0
        while pos < len(line):
            if inline_open:
                end = line.find("`$", pos)
                body = line[pos:] if end < 0 else line[pos:end]
                if is_table and re.search(r"(?<!\\)\|", body):
                    errors.append({"line": number, "issue": "unescaped table pipe inside math"})
                if end < 0:
                    break
                inline_open = False
                pos = end + 2
                continue
            if line.startswith("$`", pos):
                counts["inline"] += 1
                inline_open = True
                pos += 2
                continue
            if line[pos] == "`":
                run = len(line[pos:]) - len(line[pos:].lstrip("`"))
                end = line.find("`" * run, pos + run)
                pos = len(line) if end < 0 else end + run
                continue
            if line[pos] == "\\" and pos + 1 < len(line):
                if line[pos + 1] in "()[]":
                    errors.append({"line": number, "issue": "use GitHub protected inline math or a math fence"})
                pos += 2
                continue
            if line[pos] == "$":
                errors.append({"line": number, "issue": "unprotected dollar delimiter or unescaped literal dollar"})
            pos += 1
        if inline_open:
            errors.append({"line": number, "issue": "inline math must close on the same line"})
            inline_open = False
    if fence:
        errors.append({"line": fence[2], "issue": "unclosed code fence"})
    return counts, errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", type=Path)
    args = parser.parse_args()
    roots = args.paths or [Path(__file__).resolve().parents[1]]
    paths = set()
    for root in roots:
        paths.update([root] if root.is_file() else root.rglob("*.md"))
    paths = sorted(p for p in paths if p.suffix.lower() == ".md" and not {".git", ".lake", "node_modules"}.intersection(p.parts))
    result = {"checker": "GitHub Markdown math delimiters", "files": len(paths), "inline": 0, "display": 0, "errors": []}
    for path in paths:
        counts, errors = inspect(path)
        for key, count in counts.items():
            result[key] += count
        result["errors"].extend({"file": str(path), **error} for error in errors)
    print(json.dumps(result, indent=2))
    return int(bool(result["errors"]))


if __name__ == "__main__":
    raise SystemExit(main())
