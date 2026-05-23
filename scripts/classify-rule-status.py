#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path


MAIN_THEOREM_RE = re.compile(
    r"(?m)^(?:private\s+)?theorem\s+(cmd_step_([A-Za-z0-9_]+)_properties)\b"
)

PROG_DEF_RE = re.compile(r"(?m)^(partial\s+def|def)\s+__eo_prog_([A-Za-z0-9_]+)\b")
CRULE_START_RE = re.compile(r"(?m)^inductive\s+CRule\s*:\s*Type\s+where\b")
CRULE_CONSTRUCTOR_RE = re.compile(r"^\s*\|\s+([A-Za-z0-9_]+)\s*:\s*CRule\b")
IDENT_SEGMENT = r"(?:«[^»]+»|[A-Za-z_][A-Za-z0-9_'!?]*)"
QUALIFIED_IDENT = rf"{IDENT_SEGMENT}(?:\.{IDENT_SEGMENT})*"
DECL_START_RE = re.compile(
    rf"^(?P<prefix>(?:(?:private|protected|noncomputable)\s+)*)"
    rf"(?P<kind>partial\s+def|theorem|lemma|def|abbrev|axiom|opaque|inductive|structure|class)\s+"
    rf"(?P<name>{QUALIFIED_IDENT})(?=\s|:|\(|\{{|:=|$)",
    re.M,
)
IMPORT_RE = re.compile(r"(?m)^import\s+(.+)$")
NAMESPACE_RE = re.compile(r"^namespace\s+(.+?)\s*$")
SECTION_RE = re.compile(r"^(?:noncomputable\s+)?section(?:\s+.+)?\s*$")
MUTUAL_RE = re.compile(r"^mutual\s*$")
END_RE = re.compile(r"^end(?:\s+(.+?))?\s*$")
IDENT_RE = re.compile(QUALIFIED_IDENT)
PROOF_GAP_RE = re.compile(
    r"(?<![A-Za-z0-9_'!?])(?:sorry|admit|sorryAx)(?![A-Za-z0-9_'!?])"
)
PROOF_GAP_DECL_KINDS = {"axiom"}
IGNORED_PROOF_GAP_FILES = frozenset(
    (
        Path("Cpc/Proofs/Canonical/Order.lean"),
    )
)


@dataclass(frozen=True)
class RuleStatus:
    rule: str
    status: str
    file: Path


@dataclass(frozen=True)
class Declaration:
    path: Path
    name: str
    full_name: str
    short_name: str
    namespace: tuple[str, ...]
    kind: str
    is_private: bool
    has_own_gap: bool
    start: int
    end: int
    text: str

    @property
    def key(self) -> tuple[Path, str, int]:
        return (self.path.resolve(), self.full_name, self.start)


@dataclass(frozen=True)
class SourceFile:
    path: Path
    text: str
    imports: tuple[str, ...]
    declarations: tuple[Declaration, ...]
    has_own_gaps: bool


@dataclass(frozen=True)
class ProofGapReport:
    gaps: tuple[str, ...]

    @property
    def has_gaps(self) -> bool:
        return bool(self.gaps)


@dataclass
class DependencyIndex:
    declarations: tuple[Declaration, ...]
    visible_paths_by_path: dict[Path, frozenset[Path]]
    public_full: dict[str, list[Declaration]]
    public_short: dict[str, list[Declaration]]
    path_full: dict[tuple[Path, str], list[Declaration]]
    path_short: dict[tuple[Path, str], list[Declaration]]

    def visible_paths(self, path: Path) -> frozenset[Path]:
        resolved = path.resolve()
        return self.visible_paths_by_path.get(resolved, frozenset((resolved,)))


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


def module_name(path: Path, root: Path) -> str:
    rel_path = path.resolve().relative_to(root)
    if rel_path.suffix != ".lean":
        raise ValueError(f"{path} is not a source file")

    return ".".join(rel_path.with_suffix("").parts)


def module_path(root: Path, module: str) -> Path | None:
    parts = module.split(".")
    if not parts or any(not part for part in parts):
        return None

    path = root.joinpath(*parts).with_suffix(".lean")
    return path if path.is_file() else None


def parse_imports(text: str) -> tuple[str, ...]:
    imports: list[str] = []
    for line in IMPORT_RE.findall(text):
        imports.extend(part for part in line.split() if part)
    return tuple(imports)


def namespace_components(name: str) -> tuple[str, ...]:
    return tuple(part for part in name.split(".") if part)


def pop_block(
    block_stack: list[tuple[str, tuple[str, ...]]],
    namespace_stack: list[str],
    end_name: str | None,
) -> None:
    if not block_stack:
        return

    if end_name is None:
        kind, components = block_stack.pop()
        if kind == "namespace":
            del namespace_stack[-len(components) :]
        return

    end_components = namespace_components(end_name)
    if not end_components:
        block_stack.pop()
        return

    if tuple(namespace_stack[-len(end_components) :]) == end_components:
        remaining = len(end_components)
        while remaining > 0 and block_stack:
            kind, components = block_stack.pop()
            if kind != "namespace":
                continue
            del namespace_stack[-len(components) :]
            remaining -= len(components)
        return

    kind, components = block_stack.pop()
    if kind == "namespace":
        del namespace_stack[-len(components) :]


def qualify_name(name: str, namespace: tuple[str, ...]) -> str:
    if name.startswith("_root_."):
        return name[len("_root_.") :]
    if not namespace:
        return name
    return ".".join((*namespace, *name.split(".")))


def short_name(name: str) -> str:
    return name.split(".")[-1]


def parse_declarations(path: Path, text: str) -> tuple[Declaration, ...]:
    namespace_stack: list[str] = []
    block_stack: list[tuple[str, tuple[str, ...]]] = []
    starts: list[tuple[int, re.Match[str], tuple[str, ...]]] = []
    offset = 0

    for line in text.splitlines(keepends=True):
        stripped = line.strip()

        match = DECL_START_RE.match(line)
        if match is not None:
            starts.append((offset, match, tuple(namespace_stack)))
        else:
            namespace_match = NAMESPACE_RE.match(stripped)
            if namespace_match is not None:
                components = namespace_components(namespace_match.group(1))
                if components:
                    namespace_stack.extend(components)
                    block_stack.append(("namespace", components))
            elif SECTION_RE.match(stripped) is not None:
                block_stack.append(("section", ()))
            elif MUTUAL_RE.match(stripped) is not None:
                block_stack.append(("mutual", ()))
            else:
                end_match = END_RE.match(stripped)
                if end_match is not None:
                    pop_block(block_stack, namespace_stack, end_match.group(1))

        offset += len(line)

    declarations: list[Declaration] = []
    for index, (start, match, namespace) in enumerate(starts):
        end = starts[index + 1][0] if index + 1 < len(starts) else len(text)
        name = match.group("name")
        full_name = qualify_name(name, namespace)
        kind = match.group("kind")
        prefix = match.group("prefix")
        declaration_text = text[start:end]
        declarations.append(
            Declaration(
                path=path.resolve(),
                name=name,
                full_name=full_name,
                short_name=short_name(full_name),
                namespace=namespace,
                kind=kind,
                is_private="private" in prefix.split(),
                has_own_gap=(
                    kind in PROOF_GAP_DECL_KINDS
                    or PROOF_GAP_RE.search(declaration_text) is not None
                ),
                start=start,
                end=end,
                text=declaration_text,
            )
        )

    return tuple(declarations)


def load_source_file(
    path: Path,
    source_cache: dict[Path, SourceFile],
) -> SourceFile:
    key = path.resolve()
    if key in source_cache:
        return source_cache[key]

    text = strip_comments_and_strings(key.read_text(encoding="utf-8"))
    declarations = parse_declarations(key, text)
    source = SourceFile(
        path=key,
        text=text,
        imports=parse_imports(text),
        declarations=declarations,
        has_own_gaps=(
            PROOF_GAP_RE.search(text) is not None
            or any(declaration.has_own_gap for declaration in declarations)
        ),
    )
    source_cache[key] = source
    return source


def load_import_closure(
    path: Path,
    root: Path,
    source_cache: dict[Path, SourceFile],
    import_cache: dict[Path, tuple[Path, ...]],
) -> tuple[Path, ...]:
    key = path.resolve()
    if key in import_cache:
        return import_cache[key]

    seen: set[Path] = set()

    def visit(current: Path) -> None:
        source = load_source_file(current, source_cache)
        for imported_module in source.imports:
            imported_path = module_path(root, imported_module)
            if imported_path is None:
                continue
            imported_path = imported_path.resolve()
            if imported_path in seen:
                continue
            seen.add(imported_path)
            visit(imported_path)

    visit(key)
    closure = tuple(sorted(seen, key=str))
    import_cache[key] = closure
    return closure


def build_dependency_index(
    target_paths: tuple[Path, ...],
    root: Path,
    source_cache: dict[Path, SourceFile],
    import_cache: dict[Path, tuple[Path, ...]],
) -> DependencyIndex:
    all_paths: set[Path] = set()
    for path in target_paths:
        resolved_path = path.resolve()
        all_paths.add(resolved_path)
        all_paths.update(
            load_import_closure(resolved_path, root, source_cache, import_cache)
        )

    paths = tuple(sorted(all_paths, key=str))
    declarations: list[Declaration] = []
    visible_paths_by_path: dict[Path, frozenset[Path]] = {}

    for source_path in paths:
        source = load_source_file(source_path, source_cache)
        declarations.extend(source.declarations)
        visible_imports = load_import_closure(
            source_path,
            root,
            source_cache,
            import_cache,
        )
        visible_paths_by_path[source_path] = frozenset(
            (source_path, *visible_imports)
        )

    public_full: dict[str, list[Declaration]] = defaultdict(list)
    public_short: dict[str, list[Declaration]] = defaultdict(list)
    path_full: dict[tuple[Path, str], list[Declaration]] = defaultdict(list)
    path_short: dict[tuple[Path, str], list[Declaration]] = defaultdict(list)

    for declaration in declarations:
        declaration_path = declaration.path.resolve()
        path_full[(declaration_path, declaration.full_name)].append(declaration)
        path_short[(declaration_path, declaration.short_name)].append(declaration)
        if not declaration.is_private:
            public_full[declaration.full_name].append(declaration)
            public_short[declaration.short_name].append(declaration)

    dependency_index = DependencyIndex(
        declarations=tuple(declarations),
        visible_paths_by_path=visible_paths_by_path,
        public_full=dict(public_full),
        public_short=dict(public_short),
        path_full=dict(path_full),
        path_short=dict(path_short),
    )
    return dependency_index


def load_dependency_index(
    target_files: tuple[Path, ...],
    root: Path,
    source_cache: dict[Path, SourceFile],
    import_cache: dict[Path, tuple[Path, ...]],
    index_cache: dict[str, DependencyIndex],
) -> DependencyIndex:
    if "project" not in index_cache:
        index_cache["project"] = build_dependency_index(
            target_files,
            root,
            source_cache,
            import_cache,
        )
    return index_cache["project"]


def declaration_has_own_gap(declaration: Declaration) -> bool:
    return declaration.has_own_gap


def is_ignored_proof_gap_file(path: Path, root: Path) -> bool:
    try:
        rel_path = path.resolve().relative_to(root).as_posix()
    except ValueError:
        return False
    return Path(rel_path) in IGNORED_PROOF_GAP_FILES


def visible_closure_has_own_gaps(
    path: Path,
    root: Path,
    source_cache: dict[Path, SourceFile],
    import_cache: dict[Path, tuple[Path, ...]],
    closure_gap_cache: dict[Path, bool],
) -> bool:
    key = path.resolve()
    if key in closure_gap_cache:
        return closure_gap_cache[key]

    visible_paths = (
        visible_path
        for visible_path in (
            key,
            *load_import_closure(key, root, source_cache, import_cache),
        )
        if not is_ignored_proof_gap_file(visible_path, root)
    )
    has_gaps = any(
        load_source_file(visible_path, source_cache).has_own_gaps
        for visible_path in visible_paths
    )
    closure_gap_cache[key] = has_gaps
    return has_gaps


def declaration_label(declaration: Declaration, root: Path) -> str:
    try:
        rel_path = declaration.path.relative_to(root)
    except ValueError:
        rel_path = declaration.path
    return f"{declaration.full_name} ({rel_path})"


def declarations_named(source: SourceFile, name: str) -> tuple[Declaration, ...]:
    return tuple(
        declaration
        for declaration in source.declarations
        if declaration.full_name == name or declaration.short_name == name
    )


def token_candidates(token: str) -> tuple[str, ...]:
    token = token.removeprefix("_root_.")
    if not token:
        return ()

    candidates = [token]
    while "." in token:
        token = token.rsplit(".", 1)[0]
        candidates.append(token)
    return tuple(candidates)


def dependency_tokens(declaration: Declaration) -> tuple[str, ...]:
    seen: set[str] = set()
    tokens: list[str] = []
    for match in IDENT_RE.finditer(declaration.text):
        for candidate in token_candidates(match.group(0)):
            if candidate in seen:
                continue
            seen.add(candidate)
            tokens.append(candidate)
    return tuple(tokens)


def filter_visible(
    declarations: list[Declaration],
    visible_paths: frozenset[Path],
) -> list[Declaration]:
    return [decl for decl in declarations if decl.path.resolve() in visible_paths]


def dedupe_declarations(declarations: list[Declaration]) -> list[Declaration]:
    seen: set[tuple[Path, str, int]] = set()
    deduped: list[Declaration] = []
    for declaration in declarations:
        if declaration.key in seen:
            continue
        seen.add(declaration.key)
        deduped.append(declaration)
    return deduped


def resolve_dependency_token(
    index: DependencyIndex,
    token: str,
    context: Declaration,
) -> list[Declaration]:
    visible_paths = index.visible_paths(context.path)
    context_path = context.path.resolve()

    def visible(candidates: list[Declaration]) -> list[Declaration]:
        return filter_visible(candidates, visible_paths)

    if "." in token:
        candidates: list[Declaration] = []
        candidates.extend(index.path_full.get((context_path, token), []))
        candidates.extend(visible(index.public_full.get(token, [])))

        if context.namespace:
            qualified = ".".join((*context.namespace, *token.split(".")))
            candidates.extend(index.path_full.get((context_path, qualified), []))
            candidates.extend(visible(index.public_full.get(qualified, [])))

        return dedupe_declarations(candidates)

    candidates = []
    if context.namespace:
        qualified = ".".join((*context.namespace, token))
        candidates.extend(index.path_full.get((context_path, qualified), []))
        candidates.extend(visible(index.public_full.get(qualified, [])))

    candidates.extend(index.path_short.get((context_path, token), []))
    candidates.extend(visible(index.public_full.get(token, [])))

    if candidates:
        return dedupe_declarations(candidates)

    return dedupe_declarations(visible(index.public_short.get(token, [])))


def find_proof_gaps(
    declaration: Declaration,
    root: Path,
    index: DependencyIndex,
    source_cache: dict[Path, SourceFile],
    import_cache: dict[Path, tuple[Path, ...]],
    closure_gap_cache: dict[Path, bool],
    declaration_gap_cache: dict[tuple[Path, str, int], frozenset[str]],
    visiting: set[tuple[Path, str, int]],
) -> frozenset[str]:
    if declaration.key in declaration_gap_cache:
        return declaration_gap_cache[declaration.key]
    if is_ignored_proof_gap_file(declaration.path, root):
        declaration_gap_cache[declaration.key] = frozenset()
        return frozenset()
    if not visible_closure_has_own_gaps(
        declaration.path,
        root,
        source_cache,
        import_cache,
        closure_gap_cache,
    ):
        declaration_gap_cache[declaration.key] = frozenset()
        return frozenset()
    if declaration.key in visiting:
        return frozenset()

    visiting.add(declaration.key)
    gaps: set[str] = set()

    if declaration_has_own_gap(declaration):
        gaps.add(declaration_label(declaration, root))
    else:
        for token in dependency_tokens(declaration):
            for dependency in resolve_dependency_token(index, token, declaration):
                if dependency.key == declaration.key:
                    continue
                gaps.update(
                    find_proof_gaps(
                        dependency,
                        root,
                        index,
                        source_cache,
                        import_cache,
                        closure_gap_cache,
                        declaration_gap_cache,
                        visiting,
                    )
                )

    visiting.remove(declaration.key)
    result = frozenset(gaps)
    declaration_gap_cache[declaration.key] = result
    return result


def load_proof_gap_report(
    path: Path,
    root: Path,
    theorem: str,
    target_files: tuple[Path, ...],
    source_cache: dict[Path, SourceFile],
    import_cache: dict[Path, tuple[Path, ...]],
    index_cache: dict[str, DependencyIndex],
    closure_gap_cache: dict[Path, bool],
    declaration_gap_cache: dict[tuple[Path, str, int], frozenset[str]],
    proof_gap_cache: dict[tuple[Path, str], ProofGapReport],
) -> ProofGapReport:
    key = (path.resolve(), theorem)
    if key in proof_gap_cache:
        return proof_gap_cache[key]

    source = load_source_file(path, source_cache)
    theorem_declarations = declarations_named(source, theorem)
    if not theorem_declarations:
        source_module = module_name(path, root)
        raise ValueError(f"Could not resolve {theorem} in {source_module}")

    gaps: set[str] = set()
    for declaration in theorem_declarations:
        if declaration_has_own_gap(declaration):
            gaps.add(declaration_label(declaration, root))

    if gaps or not visible_closure_has_own_gaps(
        path,
        root,
        source_cache,
        import_cache,
        closure_gap_cache,
    ):
        report = ProofGapReport(tuple(sorted(gaps)))
        proof_gap_cache[key] = report
        return report

    index = load_dependency_index(
        target_files,
        root,
        source_cache,
        import_cache,
        index_cache,
    )
    for declaration in theorem_declarations:
        gaps.update(
            find_proof_gaps(
                declaration,
                root,
                index,
                source_cache,
                import_cache,
                closure_gap_cache,
                declaration_gap_cache,
                set(),
            )
        )

    report = ProofGapReport(tuple(sorted(gaps)))
    proof_gap_cache[key] = report
    return report


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


def load_rule_filter(path: Path) -> frozenset[str]:
    rules: set[str] = set()
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        rule = line.strip()
        if not rule or rule.startswith("#"):
            continue
        if any(ch.isspace() for ch in rule):
            raise ValueError(
                f"Invalid rule name in filter file {path} on line {line_number}: {line!r}"
            )
        rules.add(rule)

    return frozenset(rules)


def classify_file(
    path: Path,
    root: Path,
    target_files: tuple[Path, ...],
    prog_cache: dict[str, dict[str, str]],
    c_rule_cache: dict[str, set[str]],
    source_cache: dict[Path, SourceFile],
    import_cache: dict[Path, tuple[Path, ...]],
    index_cache: dict[str, DependencyIndex],
    closure_gap_cache: dict[Path, bool],
    declaration_gap_cache: dict[tuple[Path, str, int], frozenset[str]],
    proof_gap_cache: dict[tuple[Path, str], ProofGapReport],
) -> list[RuleStatus]:
    module = module_root(path, root)
    if module is None:
        raise ValueError(f"{path} is not inside the repository rooted at {root}")

    if module not in prog_cache:
        prog_cache[module] = load_prog_kinds(root, module)
    if module not in c_rule_cache:
        c_rule_cache[module] = load_crule_names(root, module)

    text = load_source_file(path, source_cache).text
    matches = list(MAIN_THEOREM_RE.finditer(text))
    results: list[RuleStatus] = []
    file_rule = path.stem.lower()

    if file_rule not in c_rule_cache[module]:
        return results

    for match in matches:
        rule = file_rule
        theorem = match.group(1)
        proof_gap_report = load_proof_gap_report(
            path,
            root,
            theorem,
            target_files,
            source_cache,
            import_cache,
            index_cache,
            closure_gap_cache,
            declaration_gap_cache,
            proof_gap_cache,
        )

        if proof_gap_report.has_gaps:
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
            "Classify proof rules as Proven, Unproven, or OutOfScope based on a "
            "recursive source scan for proof gaps in their cmd_step_<rule>_properties "
            "theorem and the __eo_prog_<rule> definition kind."
        )
    )
    parser.add_argument("path", help="Rule file or directory to scan")
    parser.add_argument(
        "--no-header",
        action="store_true",
        help="Omit the TSV header row",
    )
    parser.add_argument(
        "--filter-file",
        type=Path,
        help=(
            "Only print rules named in this file. The file should contain one rule "
            "name per line; blank lines and lines beginning with # are ignored."
        ),
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
    rule_filter: frozenset[str] | None = None
    if args.filter_file is not None:
        filter_path = args.filter_file.resolve()
        if not filter_path.exists():
            print(f"error: filter file does not exist: {filter_path}", file=sys.stderr)
            return 2
        if not filter_path.is_file():
            print(f"error: filter file is not a file: {filter_path}", file=sys.stderr)
            return 2
        try:
            rule_filter = load_rule_filter(filter_path)
        except ValueError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 2

    target_files = tuple(iter_rule_files(target))
    prog_cache: dict[str, dict[str, str]] = {}
    c_rule_cache: dict[str, set[str]] = {}
    source_cache: dict[Path, SourceFile] = {}
    import_cache: dict[Path, tuple[Path, ...]] = {}
    index_cache: dict[str, DependencyIndex] = {}
    closure_gap_cache: dict[Path, bool] = {}
    declaration_gap_cache: dict[tuple[Path, str, int], frozenset[str]] = {}
    proof_gap_cache: dict[tuple[Path, str], ProofGapReport] = {}
    statuses: list[RuleStatus] = []

    try:
        for file_path in target_files:
            statuses.extend(
                classify_file(
                    file_path,
                    root,
                    target_files,
                    prog_cache,
                    c_rule_cache,
                    source_cache,
                    import_cache,
                    index_cache,
                    closure_gap_cache,
                    declaration_gap_cache,
                    proof_gap_cache,
                )
            )
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    statuses.sort(key=lambda entry: (entry.rule, str(entry.file)))
    if rule_filter is not None:
        statuses = [entry for entry in statuses if entry.rule in rule_filter]

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
