#!/usr/bin/env python3
"""Executive summary of lines of code and proof in Cpc/.

Reports, by transitive Lean `import` closure (restricted to the `Cpc` library):

  (1) Lines to *define* eo_satisfiability: Spec.lean and its dependencies.
  (2) Lines for the proof *checker*: Logos.lean and its dependencies.
  (3) Lines for the central proof of correctness of the checker, partitioned
      into disjoint buckets (no file double-counted):
        (a) smt-model-eval type preservation
        (b) translation type preservation
        (c) canonicity theorem
        (d) non-vacuity
        (e) proofs of proof rule correctness
        (f) top-level checker correctness (the driver tying it together)

Attribution for (3) is priority-based: the definitions from (1)+(2) are
excluded first, then each file is owned by the earliest bucket whose import
closure reaches it (order a -> b -> c -> d -> f -> e). So the shared
type-preservation foundation is counted once under (a), and b/c/d/e/f report
only their *incremental* lines. The buckets are disjoint and sum to the whole
proof.

A "line of code" is a non-blank, non-comment line (Lean line comments `--` and
nested block comments `/- ... -/` are stripped).

Usage:
  scripts/cpc-loc-summary.py            # summary (totals + per-bucket)
  scripts/cpc-loc-summary.py --files    # also list every file with its LOC
"""

from __future__ import annotations

import os
import re
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(SCRIPT_DIR)

# --- Bucket configuration -------------------------------------------------
# Each entry is (key, title, closure_roots, file_roots). Buckets are processed
# in this order; a file is attributed to the first bucket (after the excluded
# definitions) that reaches it. A bucket owns the import closure of its
# `closure_roots` plus the literal modules in `file_roots`, minus anything an
# earlier bucket already claimed.
#
# `file_roots` (literal, not closure) is how the top-level glue is captured
# without swallowing the rules: Checker.lean / RuleLemmas.lean import every
# rule, so their *closures* would absorb all of (e). We attribute just those
# two files to (f) and let the rule leaves fall through to (e). CheckerCore's
# closure, by contrast, is pure scaffolding (no rule leaves) so it is safe to
# expand.
PROOF_BUCKETS = [
    ("a", "smt-model-eval type preservation", ["Cpc.Proofs.TypePreservation"], []),
    ("b", "translation type preservation",    ["Cpc.Proofs.Translation"], []),
    ("c", "canonicity theorem",               ["Cpc.Proofs.Canonical"], []),
    ("d", "non-vacuity",                       ["Cpc.Proofs.TypePreservation.Nonvacuity"], []),
    ("f", "top-level checker correctness",     ["Cpc.Proofs.CheckerCore"],
                                               ["Cpc.Proofs.Checker", "Cpc.Proofs.RuleLemmas"]),
    ("e", "proofs of proof rule correctness",  ["Cpc.Proofs.Checker"], []),  # catch-all
]

# The full central proof (everything reachable from the top-level theorem).
CENTRAL_ROOTS = ["Cpc.Proofs.Checker"]

# Definitions to exclude from the proof partition (reported as (1) and (2)).
SPEC_ROOTS = ["Cpc.Spec"]
LOGOS_ROOTS = ["Cpc.Logos"]


# --- Import graph ---------------------------------------------------------
IMPORT_RE = re.compile(r"^\s*import\s+(Cpc[\w.]+)")


def module_to_path(module: str) -> str:
    return os.path.join(REPO_ROOT, module.replace(".", "/") + ".lean")


def path_to_module(path: str) -> str:
    rel = os.path.relpath(path, REPO_ROOT)
    return rel[:-len(".lean")].replace("/", ".")


def build_graph() -> tuple[dict[str, set[str]], set[str]]:
    imports: dict[str, set[str]] = {}
    modules: set[str] = set()
    cpc_dir = os.path.join(REPO_ROOT, "Cpc")
    for dirpath, _, files in os.walk(cpc_dir):
        for name in files:
            if not name.endswith(".lean"):
                continue
            path = os.path.join(dirpath, name)
            module = path_to_module(path)
            modules.add(module)
            deps: set[str] = set()
            with open(path, encoding="utf-8") as fh:
                for line in fh:
                    m = IMPORT_RE.match(line)
                    if m:
                        deps.add(m.group(1))
            imports[module] = deps
    return imports, modules


def closure(roots, imports, modules) -> set[str]:
    seen: set[str] = set()
    stack = list(roots)
    while stack:
        module = stack.pop()
        if module in seen or module not in modules:
            continue
        seen.add(module)
        stack.extend(imports.get(module, ()))
    return seen


# --- LOC counting (non-blank, non-comment, Lean-aware) --------------------
def count_loc(path: str) -> int:
    """Count non-blank, non-comment lines, stripping Lean comments.

    Handles `--` line comments and nested `/- ... -/` block comments
    (docstrings `/-- -/` are block comments too). Does not special-case `--`
    inside string literals, which is rare in proof code.
    """
    with open(path, encoding="utf-8") as fh:
        text = fh.read()

    out: list[str] = []
    i = 0
    n = len(text)
    depth = 0  # block-comment nesting depth
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0:
            if text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        # not in a block comment
        if text.startswith("--", i):
            # skip to end of line (line comment)
            while i < n and text[i] != "\n":
                i += 1
            continue
        out.append(text[i])
        i += 1

    count = 0
    for line in "".join(out).splitlines():
        if line.strip():
            count += 1
    return count


def loc_of(module: str, cache: dict[str, int]) -> int:
    if module in cache:
        return cache[module]
    path = module_to_path(module)
    value = count_loc(path) if os.path.exists(path) else 0
    cache[module] = value
    return value


def total_loc(modules, cache) -> int:
    return sum(loc_of(m, cache) for m in modules)


# --- Reporting ------------------------------------------------------------
def print_file_list(modules, cache, indent="    "):
    for module in sorted(modules, key=lambda m: (-loc_of(m, cache), m)):
        print(f"{indent}{loc_of(module, cache):6d}  {module}")


def main() -> int:
    show_files = "--files" in sys.argv[1:]

    imports, modules = build_graph()
    cache: dict[str, int] = {}

    spec_cl = closure(SPEC_ROOTS, imports, modules)
    logos_cl = closure(LOGOS_ROOTS, imports, modules)
    central_cl = closure(CENTRAL_ROOTS, imports, modules)

    print("=" * 70)
    print("CPC executive summary  (LOC = non-blank, non-comment lines)")
    print("=" * 70)

    # (1) eo_satisfiability definition
    print("\n(1) Definition of eo_satisfiability  [Cpc.Spec + dependencies]")
    print(f"    files: {len(spec_cl):4d}    lines: {total_loc(spec_cl, cache):7d}")
    print_file_list(spec_cl, cache)

    # (2) proof checker
    print("\n(2) Proof checker  [Cpc.Logos + dependencies]")
    print(f"    files: {len(logos_cl):4d}    lines: {total_loc(logos_cl, cache):7d}")
    print_file_list(logos_cl, cache)

    # (3) central proof of correctness, partitioned.
    # The "proof universe" is everything reachable from the top-level theorem
    # PLUS the bucket roots. Non-vacuity (d) is a standalone meta-theorem that
    # nothing imports, so it is not in the central closure but is still part of
    # the correctness story the buckets account for.
    excluded = spec_cl | logos_cl
    print("\n(3) Central proof of correctness of the checker")
    print("    (definitions from (1)+(2) excluded; buckets disjoint, priority-attributed)")

    claimed = set(excluded)
    results = []
    for key, title, closure_roots, file_roots in PROOF_BUCKETS:
        bucket_cl = closure(closure_roots, imports, modules)
        bucket_cl |= {m for m in file_roots if m in modules}
        own = bucket_cl - claimed
        claimed |= own
        results.append((key, title, own))

    proof_total = total_loc(claimed - excluded, cache)
    proof_files = len(claimed - excluded)
    print(f"    total proof files: {proof_files:4d}    total proof lines: {proof_total:7d}")

    for key, title, own in results:
        note = "  (standalone; not imported by the top-level theorem)" if key == "d" else ""
        print(f"\n    ({key}) {title}{note}")
        print(f"        files: {len(own):4d}    lines: {total_loc(own, cache):7d}")
        if show_files:
            print_file_list(own, cache, indent="        ")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
