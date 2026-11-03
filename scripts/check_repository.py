#!/usr/bin/env python3
"""Check that the Lean library is wired and contains no unsanctioned holes."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys
import unicodedata


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
UMBRELLA = REPOSITORY_ROOT / "VOA.lean"
SOURCE_ROOT = REPOSITORY_ROOT / "VOA"
ALLOWED_AXIOM_FILE = SOURCE_ROOT / "Foundations" / "AffineLie.lean"
FORBIDDEN_TOKENS = frozenset(
    {"sorry", "admit", "native_decide", "stop", "implemented_by"}
)
_SPECIAL = re.compile(r'''--|/-|r#+"|'|"''')
_BLOCK_DELIMITER = re.compile(r"/-|-/")
_STRING_DELIMITER = re.compile(r'''\\[\s\S]|"''')


@dataclass(frozen=True)
class Token:
    value: str
    line: int
    column: int


@dataclass(frozen=True)
class Import:
    module: str
    line: int


class LexicalError(ValueError):
    """A malformed comment or string prevented reliable scanning."""

    def __init__(self, message: str, text: str, offset: int) -> None:
        line = text.count("\n", 0, offset) + 1
        previous_newline = text.rfind("\n", 0, offset)
        column = offset - previous_newline
        super().__init__(f"{line}:{column}: {message}")


def _is_identifier_start(character: str) -> bool:
    if character.isascii():
        return character == "_" or "A" <= character <= "Z" or "a" <= character <= "z"
    category = unicodedata.category(character)
    return category.startswith("L")


def _is_identifier_continue(character: str) -> bool:
    if character.isascii():
        return (
            character == "_"
            or character == "'"
            or "A" <= character <= "Z"
            or "a" <= character <= "z"
            or "0" <= character <= "9"
        )
    category = unicodedata.category(character)
    return (
        _is_identifier_start(character)
        or character == "'"
        or category.startswith("M")
        or category.startswith("N")
        or category == "Pc"
    )


def _blank(output: list[str], source: str, start: int, end: int) -> None:
    """Blank a span while retaining line endings and therefore source positions."""
    for index in range(start, end):
        if source[index] not in "\r\n":
            output[index] = " "


def _char_literal_end(source: str, start: int) -> int | None:
    """Return the end of a plausible Lean character literal, if present."""
    if start + 2 >= len(source) or source[start] != "'":
        return None

    index = start + 1
    escaped = source[index] == "\\"
    if escaped:
        index += 1
        while index < len(source) and source[index] not in "'\r\n":
            index += 1
    else:
        index += 1

    if index < len(source) and source[index] == "'":
        return index + 1
    return None


def mask_comments_and_literals(source: str) -> str:
    """Replace Lean comments and literals with spaces, preserving positions.

    Lean block comments nest. Ordinary, triple-quoted, and raw strings are
    recognized; character literals are masked too so a quoted double quote is
    not mistaken for the beginning of a string.
    """
    output = list(source)
    index = 0
    length = len(source)

    while index < length:
        special = _SPECIAL.search(source, index)
        if special is None:
            break
        index = special.start()
        marker = special.group(0)

        if marker == "--":
            end = source.find("\n", special.end())
            if end == -1:
                end = length
            _blank(output, source, index, end)
            index = end
            continue

        if marker == "/-":
            start = index
            depth = 1
            index = special.end()
            while depth:
                delimiter = _BLOCK_DELIMITER.search(source, index)
                if delimiter is None:
                    raise LexicalError("unterminated block comment", source, start)
                if delimiter.group(0) == "/-":
                    depth += 1
                else:
                    depth -= 1
                index = delimiter.end()
            _blank(output, source, start, index)
            continue

        if marker.startswith("r#") and (
            index == 0 or not _is_identifier_continue(source[index - 1])
        ):
            start = index
            hashes = marker[1:-1]
            index = special.end()
            terminator = '"' + hashes
            end = source.find(terminator, index)
            if end == -1:
                raise LexicalError("unterminated raw string literal", source, start)
            index = end + len(terminator)
            _blank(output, source, start, index)
            continue

        if marker.startswith("r#"):
            # It was attached to an identifier and therefore was not a raw
            # string prefix. Resume before its quote so that quote is scanned.
            index += 1
            continue

        if marker == '"' and source.startswith('"""', index):
            start = index
            index += 3
            end = source.find('"""', index)
            if end == -1:
                raise LexicalError("unterminated triple-quoted string literal", source, start)
            index = end + 3
            _blank(output, source, start, index)
            continue

        if marker == '"':
            start = index
            index += 1
            while True:
                delimiter = _STRING_DELIMITER.search(source, index)
                if delimiter is None:
                    raise LexicalError("unterminated string literal", source, start)
                index = delimiter.end()
                if delimiter.group(0) == '"':
                    break
            _blank(output, source, start, index)
            continue

        if marker == "'" and (
            index == 0 or not _is_identifier_continue(source[index - 1])
        ):
            end = _char_literal_end(source, index)
            if end is not None:
                _blank(output, source, index, end)
                index = end
                continue

        index = special.end()

    return "".join(output)


def tokenize(source: str) -> list[Token]:
    """Return the code tokens needed by the policy checks."""
    masked = mask_comments_and_literals(source)
    tokens: list[Token] = []
    index = 0
    line = 1
    column = 1

    while index < len(masked):
        character = masked[index]
        if character == "\n":
            index += 1
            line += 1
            column = 1
            continue
        if character.isspace():
            index += 1
            column += 1
            continue

        token_line = line
        token_column = column
        if character == "«":
            end = masked.find("»", index + 1)
            end = len(masked) if end == -1 else end + 1
        elif _is_identifier_start(character):
            end = index + 1
            while end < len(masked) and _is_identifier_continue(masked[end]):
                end += 1
        else:
            end = index + 1

        value = masked[index:end]
        tokens.append(Token(value, token_line, token_column))
        column += end - index
        index = end

    return tokens


def parse_imports(source: str) -> list[Import]:
    """Extract imports from Lean import commands after lexical masking."""
    masked = mask_comments_and_literals(source)
    imports: list[Import] = []
    module_pattern = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")

    for line_number, line in enumerate(masked.splitlines(), start=1):
        command = re.match(
            r"^[ \t]*(?:(?:public|meta)[ \t]+)*import(?:[ \t]+(.*))?$",
            line,
        )
        if command is None or command.group(1) is None:
            continue
        for match in module_pattern.finditer(command.group(1)):
            imports.append(Import(match.group(0), line_number))
    return imports


def _module_name(path: Path) -> str:
    relative = path.relative_to(REPOSITORY_ROOT).with_suffix("")
    return ".".join(relative.parts)


def _display_path(path: Path) -> str:
    return path.relative_to(REPOSITORY_ROOT).as_posix()


def check_reachability(
    source_files: list[Path],
) -> tuple[set[Path], list[str], list[Path], int]:
    """Traverse local imports from the umbrella and report graph problems."""
    module_paths = {_module_name(path): path for path in [UMBRELLA, *source_files]}
    reachable: set[Path] = set()
    pending = [UMBRELLA]
    missing_imports: list[str] = []
    import_edges = 0

    while pending:
        path = pending.pop()
        if path in reachable:
            continue
        reachable.add(path)
        source = path.read_text(encoding="utf-8")
        for imported in parse_imports(source):
            if not (
                imported.module == "VOA"
                or imported.module.startswith("VOA.")
            ):
                continue
            import_edges += 1
            imported_path = module_paths.get(imported.module)
            if imported_path is None:
                missing_imports.append(
                    f"{_display_path(path)}:{imported.line}: local import "
                    f"'{imported.module}' has no corresponding Lean file"
                )
            elif imported_path not in reachable:
                pending.append(imported_path)

    unreachable = sorted(set(source_files) - reachable)
    return reachable, missing_imports, unreachable, import_edges


def check_source_policy(source_files: list[Path]) -> tuple[list[str], int]:
    """Reject proof-hole tokens and every axiom declaration."""
    diagnostics: list[str] = []
    sanctioned_axioms = 0

    for path in [UMBRELLA, *source_files]:
        source = path.read_text(encoding="utf-8")
        try:
            tokens = tokenize(source)
        except LexicalError as error:
            diagnostics.append(f"{_display_path(path)}:{error}")
            continue

        for token_index, token in enumerate(tokens):
            if token.value in FORBIDDEN_TOKENS:
                location = f"{_display_path(path)}:{token.line}:{token.column}"
                diagnostics.append(
                    f"{location}: forbidden code token '{token.value}'"
                )
                continue

            if token.value != "axiom":
                continue
            location = f"{_display_path(path)}:{token.line}:{token.column}"
            declared_name = (
                tokens[token_index + 1].value
                if token_index + 1 < len(tokens)
                else "<missing>"
            )
            # `VOA.pbw` is a theorem since 2026-10-19: no axiom declaration is allowed.
            diagnostics.append(
                f"{location}: axiom declaration '{declared_name}' "
                "(the project has no sanctioned axioms)"
            )

    return diagnostics, sanctioned_axioms


def main() -> int:
    if not UMBRELLA.is_file() or not SOURCE_ROOT.is_dir():
        print(
            "repository check failed: expected VOA.lean and VOA/ "
            f"under {REPOSITORY_ROOT}",
            file=sys.stderr,
        )
        return 1

    source_files = sorted(SOURCE_ROOT.rglob("*.lean"))
    try:
        reachable, missing_imports, unreachable, import_edges = check_reachability(
            source_files
        )
    except LexicalError as error:
        print(f"repository check failed while reading imports: {error}", file=sys.stderr)
        return 1

    policy_diagnostics, sanctioned_axioms = check_source_policy(source_files)
    failed = bool(missing_imports or unreachable or policy_diagnostics)

    if missing_imports:
        print("Missing local imports:", file=sys.stderr)
        for diagnostic in missing_imports:
            print(f"  {diagnostic}", file=sys.stderr)

    if unreachable:
        print(
            f"Unreachable Lean files ({len(unreachable)}):",
            file=sys.stderr,
        )
        for path in unreachable:
            print(f"  {_display_path(path)}", file=sys.stderr)
        print(
            "  Import these files (transitively) from VOA.lean, or remove "
            "them from VOA/.",
            file=sys.stderr,
        )

    if policy_diagnostics:
        print("Lean source policy violations:", file=sys.stderr)
        for diagnostic in policy_diagnostics:
            print(f"  {diagnostic}", file=sys.stderr)

    reachable_modules = len(reachable - {UMBRELLA})
    summary = (
        f"{len(source_files)} library files scanned; "
        f"{reachable_modules} reachable through {import_edges} local import edges; "
        f"{sanctioned_axioms} sanctioned axiom declaration(s)"
    )
    if failed:
        print(f"Repository check failed: {summary}.", file=sys.stderr)
        return 1

    print(f"Repository check passed: {summary}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
