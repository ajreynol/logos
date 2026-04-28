#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path


MAIN_THEOREM_RE = re.compile(
    r"(?m)^(?:private\s+)?theorem\s+(cmd_step_([A-Za-z0-9_]+)_properties)\b"
)

PROG_DEF_RE = re.compile(r"(?m)^(partial\s+def|def)\s+__eo_prog_([A-Za-z0-9_]+)\b")
CRULE_START_RE = re.compile(r"(?m)^inductive\s+CRule\s*:\s*Type\s+where\b")
CRULE_CONSTRUCTOR_RE = re.compile(r"^\s*\|\s+([A-Za-z0-9_]+)\s*:\s*CRule\b")
SORRY_RE = re.compile(r"\b(?:sorry|admit)\b")


@dataclass(frozen=True)
class RuleStatus:
    rule: str
    status: str
    file: Path


def strip_comments_and_strings(text: str) -> str:
    """Replace comments and strings with whitespace while preserving newlines."""
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_string = False

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend((" ", " "))
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            if ch == "\\" and i + 1 < n:
                out.extend((" ", " "))
                i += 2
            elif ch == "\"":
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if ch == "/" and nxt == "-":
            block_depth = 1
            out.extend((" ", " "))
            i += 2
            continue

        if ch == "-" and nxt == "-":
            out.extend((" ", " "))
            i += 2
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue

        if ch == "\"":
            in_string = True
            out.append(" ")
            i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def module_root(path: Path, root: Path) -> str | None:
    try:
        return path.resolve().relative_to(root).parts[0]
    except ValueError:
        return None


def load_prog_kinds(root: Path, module: str) -> dict[str, str]:
    logos_path = root / module / "Logos.lean"
    if not logos_path.is_file():
        return {}

    text = strip_comments_and_strings(logos_path.read_text(encoding="utf-8"))
    prog_kinds: dict[str, str] = {}

    for kind, rule in PROG_DEF_RE.findall(text):
        prog_kinds[rule] = kind

    return prog_kinds


def load_crule_names(root: Path, module: str) -> set[str]:
    logos_path = root / module / "Logos.lean"
    if not logos_path.is_file():
        return set()

    text = strip_comments_and_strings(logos_path.read_text(encoding="utf-8"))
    start_match = CRULE_START_RE.search(text)
    if start_match is None:
        return set()

    names: set[str] = set()
    for line in text[start_match.end() :].splitlines():
        if not line.strip():
            continue
        if not line[:1].isspace():
            break
        constructor_match = CRULE_CONSTRUCTOR_RE.match(line)
        if constructor_match is not None:
            names.add(constructor_match.group(1))

    return names


def classify_file(
    path: Path,
    root: Path,
    prog_cache: dict[str, dict[str, str]],
    c_rule_cache: dict[str, set[str]],
) -> list[RuleStatus]:
    module = module_root(path, root)
    if module is None:
        raise ValueError(f"{path} is not inside the repository rooted at {root}")

    if module not in prog_cache:
        prog_cache[module] = load_prog_kinds(root, module)
    if module not in c_rule_cache:
        c_rule_cache[module] = load_crule_names(root, module)

    text = strip_comments_and_strings(path.read_text(encoding="utf-8"))
    matches = list(MAIN_THEOREM_RE.finditer(text))
    results: list[RuleStatus] = []
    file_rule = path.stem.lower()
    file_has_sorry = SORRY_RE.search(text) is not None

    if file_rule not in c_rule_cache[module]:
        return results

    for _match in matches:
        rule = file_rule

        if file_has_sorry:
            prog_kind = prog_cache[module].get(rule)
            if prog_kind == "partial def":
                status = "OutOfScope"
            elif prog_kind == "def":
                status = "Unproven"
            else:
                raise ValueError(
                    f"Could not resolve __eo_prog_{rule} in {root / module / 'Logos.lean'}"
                )
        else:
            status = "Proven"

        results.append(RuleStatus(rule=rule, status=status, file=path))

    return results


def iter_rule_files(target: Path) -> list[Path]:
    if target.is_file():
        return [target] if target.suffix == ".lean" else []

    return sorted(path for path in target.rglob("*.lean") if path.is_file())


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Classify Lean proof rules as Proven, Unproven, or OutOfScope based on "
            "their cmd_step_<rule>_properties theorem and __eo_prog_<rule> definition."
        )
    )
    parser.add_argument("path", help="Rule file or directory to scan")
    parser.add_argument(
        "--no-header",
        action="store_true",
        help="Omit the TSV header row",
    )
    parser.add_argument(
        "-proven",
        action="store_true",
        dest="only_proven",
        help="Print only Proven rules as a simple list",
    )
    parser.add_argument(
        "-unproven",
        action="store_true",
        dest="only_unproven",
        help="Print only Unproven rules as a simple list",
    )
    parser.add_argument(
        "-outofscope",
        action="store_true",
        dest="only_outofscope",
        help="Print only OutOfScope rules as a simple list",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = repo_root()
    target = Path(args.path).resolve()

    if not target.exists():
        print(f"error: path does not exist: {target}", file=sys.stderr)
        return 2

    prog_cache: dict[str, dict[str, str]] = {}
    c_rule_cache: dict[str, set[str]] = {}
    statuses: list[RuleStatus] = []

    try:
        for file_path in iter_rule_files(target):
            statuses.extend(classify_file(file_path, root, prog_cache, c_rule_cache))
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    statuses.sort(key=lambda entry: (entry.rule, str(entry.file)))

    wanted_statuses: set[str] = set()
    if args.only_proven:
        wanted_statuses.add("Proven")
    if args.only_unproven:
        wanted_statuses.add("Unproven")
    if args.only_outofscope:
        wanted_statuses.add("OutOfScope")

    if wanted_statuses:
        seen: set[str] = set()
        for entry in statuses:
            if entry.status not in wanted_statuses or entry.rule in seen:
                continue
            seen.add(entry.rule)
            print(entry.rule)
        return 0

    if not args.no_header:
        print("rule\tstatus")

    for entry in statuses:
        print(f"{entry.rule}\t{entry.status}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
