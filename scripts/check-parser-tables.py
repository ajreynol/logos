#!/usr/bin/env python3
"""Check a generated parser configuration against the generated signature.

`Cpc/Parser.lean` and `CpcMini/Parser.lean` are auto-generated from the same
Eunoia signature as `Cpc/Logos.lean` and `CpcMini/Logos.lean`.  This script
re-derives from the signature the facts the generator has to get right, and
fails if the parser table disagrees:

  * every operator of the signature is declared exactly once;
  * every proof rule of the calculus is named exactly once;
  * an operator whose *first* parameter is a `@@TypedList` is declared with the
    gathered-list arity `.listArg`, and no other operator is.

The last one is the surface-syntax policy for n-ary operators.  Eunoia declares
`distinct` as `(-> (@@TypedList T) Bool)` and `set.insert` as
`(-> (@@TypedList T) (Set T) (Set T))`, but SMT-LIB writes `(distinct a b c)`
and `(set.insert a b c S)` rather than the desugared list, so the parser has to
gather the leading arguments.  Deriving the arity from the arrow shape alone
loses that, which is how `@@TypedList` ended up leaking into input proofs.

Operators whose *later* parameters are `@@TypedList`s are reported too: the list
constructors themselves are expected (`@@TypedList.cons` is n-ary in its own
right), but anything else is a shape the parser's arity model cannot express.

Usage: scripts/check-parser-tables.py [Cpc ...]
"""

from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# The list constructors are declared over `@@TypedList` but build one rather
# than consume one, so the gathered-list policy does not apply to them.
LIST_BUILTINS = {
    "UserOp._at__at_TypedList",
    "UserOp._at__at_TypedList_nil",
    "UserOp._at__at_TypedList_cons",
}

TYPED_LIST_PARAM = re.compile(r"^\(Term\.Apply\s*\(Term\.UOp\s+UserOp\._at__at_TypedList\)")


def inductive_constructors(source: str, name: str) -> list[str]:
    """The constructor names of `inductive <name>`, in declaration order."""
    start = source.index(f"inductive {name} : Type where")
    body = source[start:]
    body = body[: body.index("deriving")]
    return re.findall(r"^\s*\|\s*([A-Za-z_0-9]+)\s*:", body, re.M)


def split_top_level(text: str, sep: str = ",") -> list[str]:
    """Split on `sep`, ignoring separators nested inside parentheses."""
    parts, depth, current = [], 0, []
    for ch in text:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch == sep and depth == 0:
            parts.append("".join(current).strip())
            current = []
        else:
            current.append(ch)
    parts.append("".join(current).strip())
    return parts


def typeof_definitions(source: str) -> dict[str, list[list[str]]]:
    """For each `__eo_typeof*` definition, the parameter patterns of each arm."""
    definitions: dict[str, list[list[str]]] = {}
    for block in source.split("\ndef "):
        name = block.split(None, 1)[0] if block.split() else ""
        if not name.startswith("__eo_typeof"):
            continue
        body = block.split("\n", 1)[1] if "\n" in block else ""
        arms = []
        for line in body.splitlines():
            match = re.match(r"\s*\|(.+?)=>", line)
            if match:
                arms.append(split_top_level(match.group(1).strip()))
        definitions[name] = arms
    return definitions


def typeof_dispatch(source: str) -> dict[str, tuple[int, str]]:
    """Map each applied `UserOp` to its argument count and its typing function.

    Read off the `__eo_typeof` dispatcher, which is generated from the same
    declarations as the parser table, so it is the authority on both.
    """
    start = source.index("\ndef __eo_typeof : Term -> Term")
    body = source[start + 1 :]
    body = body[: body.index("\n\n\ndef ")] if "\n\n\ndef " in body else body
    dispatch: dict[str, tuple[int, str]] = {}
    for line in body.splitlines():
        match = re.match(r"\s*\|\s*(.+?)\s*=>\s*(.*)$", line)
        if not match:
            continue
        pattern, result = match.groups()
        op = re.search(r"Term\.UOp\s+(UserOp\.[A-Za-z_0-9]+)\)", pattern)
        callee = re.search(r"\((__eo_typeof[A-Za-z_0-9]+)", result)
        if not op or not callee:
            continue
        dispatch[op.group(1)] = (pattern.count("Term.Apply"), callee.group(1))
    return dispatch


def parser_entries(source: str) -> list[dict]:
    """The operator declarations of a generated parser table."""
    start = source.index("private def parserOps")
    table = source[start : source.index("/-- The proof rules of the calculus")]
    entries = []
    for chunk in table.split("\n  { name := ")[1:]:
        name = re.match(r'"((?:[^"\\]|\\.)*)"', chunk).group(1)
        # `arity` may itself mention operators (a chainable's chaining operator,
        # a gathered list's constructor), so only `build` says what is declared.
        build = chunk.split("build :=", 1)[1] if "build :=" in chunk else ""
        arity = chunk.split("arity :=", 1)[1].split("build :=")[0].strip()
        entries.append(
            {
                "name": name,
                "arity": arity,
                "ops": re.findall(r"\b(UserOp[123]?\.[A-Za-z_0-9]+)", build),
            }
        )
    return entries


def check(calculus: str) -> list[str]:
    errors: list[str] = []
    term_src = (REPO_ROOT / calculus / "LogosTerm.lean").read_text()
    logos_src = (REPO_ROOT / calculus / "Logos.lean").read_text()
    parser_src = (REPO_ROOT / calculus / "Parser.lean").read_text()

    # 1. Operator coverage.
    declared: list[str] = []
    for family in ["UserOp", "UserOp1", "UserOp2", "UserOp3"]:
        # `None` is the generator's placeholder for a family with no members, so
        # it has no surface syntax and no entry in the parser table.
        declared += [
            f"{family}.{c}" for c in inductive_constructors(term_src, family) if c != "None"
        ]
    entries = parser_entries(parser_src)
    referenced = Counter(op for entry in entries for op in entry["ops"])
    for op in declared:
        if referenced[op] == 0:
            errors.append(f"operator {op} is not declared in the parser table")
        elif referenced[op] > 1:
            errors.append(f"operator {op} is declared {referenced[op]} times")
    for op in referenced:
        if op not in declared:
            errors.append(f"parser table declares {op}, which the signature does not")

    # 2. Rule coverage.
    rules = inductive_constructors(logos_src, "CRule")
    table = parser_src[parser_src.index("private def parserRules") :]
    table = table[: table.index("\n]")]
    named = Counter(c for _, c in re.findall(r'\("([^"]+)",\s*\.([A-Za-z_0-9]+)\)', table))
    for rule in rules:
        if named[rule] == 0:
            errors.append(f"rule {rule} is not named in the parser table")
        elif named[rule] > 1:
            errors.append(f"rule {rule} is named {named[rule]} times")
    for rule in named:
        if rule not in rules:
            errors.append(f"parser table names rule {rule}, which the calculus does not have")

    # 3. The gathered-list policy for operators declared over a `@@TypedList`.
    definitions = typeof_definitions(logos_src)
    expected: dict[str, int] = {}
    for op, (nargs, callee) in typeof_dispatch(logos_src).items():
        if op in LIST_BUILTINS:
            continue
        arms = definitions.get(callee, [])
        if any(arm and TYPED_LIST_PARAM.match(arm[0]) for arm in arms):
            expected[op] = nargs - 1
        elif any(TYPED_LIST_PARAM.match(param) for arm in arms for param in arm[1:]):
            errors.append(
                f"{op} takes a @@TypedList in a position other than the first, "
                f"which the parser's arity model cannot express"
            )

    actual: dict[str, int] = {}
    for entry in entries:
        match = re.match(r"\.listArg\s+(\d+)\b", entry["arity"])
        if match:
            for op in entry["ops"]:
                actual[op] = int(match.group(1))

    arity_of = {op: entry["arity"] for entry in entries for op in entry["ops"]}
    for op, rest in expected.items():
        if op not in actual:
            errors.append(
                f"{op} is declared over a @@TypedList, so it must use .listArg {rest}, "
                f"but the parser table says {arity_of.get(op, 'nothing')}"
            )
        elif actual[op] != rest:
            errors.append(f"{op} uses .listArg {actual[op]} but takes {rest} further arguments")
    for op in actual:
        if op not in expected:
            errors.append(f"{op} uses .listArg but is not declared over a @@TypedList")

    return errors


def main(argv: list[str]) -> int:
    calculi = argv[1:] or ["Cpc", "CpcMini"]
    status = 0
    for calculus in calculi:
        errors = check(calculus)
        if errors:
            status = 1
            print(f"{calculus}/Parser.lean disagrees with the signature:", file=sys.stderr)
            for error in errors:
                print(f"  {error}", file=sys.stderr)
        else:
            print(f"{calculus}/Parser.lean agrees with the signature.")
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv))
