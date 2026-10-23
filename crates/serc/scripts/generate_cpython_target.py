#!/usr/bin/env python3
"""Generate the bytecode target metadata for the pinned CPython release."""

from __future__ import annotations

import argparse
import ast
import difflib
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from types import SimpleNamespace

# Resolve only adjacent, repository-owned generator helpers, including with -P/-I.
sys.path.insert(0, str(Path(__file__).resolve().parent))

TARGET_TAG = "v3.14.5"
TARGET_COMMIT = "5607950ef232dad16d75c0cf53101d9649d89115"
TARGET_VERSION = (3, 14, 5)
TARGET_MINOR = "3.14"
TARGETS = {
    "3.12": (
        "v3.12.14",
        "2abcf904b8dac8c999d2b3aac76681abb333798a",
        (3, 12, 14),
        4,
    ),
    "3.13": (
        "v3.13.15",
        "4061bc4c35f7c26f25264666d4ba083b93d2f6f9",
        (3, 13, 15),
        4,
    ),
    "3.14": (TARGET_TAG, TARGET_COMMIT, TARGET_VERSION, 5),
    "3.15": (
        "v3.15.0rc2",
        "435c9e5a798c99653e3ab64ce29baed0e4f3dfee",
        (3, 15, 0),
        6,
    ),
}
TARGET_INPUTS = (
    "Include/opcode_ids.h",
    "Include/opcode.h",
    "Include/object.h",
    "Include/ceval.h",
    "Include/internal/pycore_opcode_metadata.h",
    "Include/internal/pycore_opcode_utils.h",
    "Include/internal/pycore_intrinsics.h",
    "Include/internal/pycore_ceval.h",
    "Include/cpython/code.h",
    "Include/internal/pycore_code.h",
    "Include/internal/pycore_magic_number.h",
    "Include/internal/pycore_global_strings.h",
    "Include/patchlevel.h",
    "Python/codegen.c",
    "Python/flowgraph.c",
    "Python/Python-ast.c",
)
MODERN_TARGET_INPUTS = TARGET_INPUTS
BOOTSTRAP_314_INPUT = "scripts/target_metadata/cpython_3_14_5_bootstrap.json"
BOOTSTRAP_314_SHA256 = (
    "3a55396a7cd0f658d221fa67528ff3390b29db386dac856640ef90b17ef9ad8a"
)
BOOTSTRAP_INPUTS = (
    "Lib/importlib/_bootstrap.py",
    "Lib/importlib/_bootstrap_external.py",
    "Lib/encodings/__init__.py",
    "Lib/encodings/aliases.py",
    "Objects/codeobject.c",
    "Python/import.c",
    "Python/pylifecycle.c",
    "Python/codecs.c",
    "Programs/_freeze_module.c",
    "Include/internal/pycore_global_strings.h",
    "Python/Python-ast.c",
)
TARGET_INPUTS = tuple(dict.fromkeys((*MODERN_TARGET_INPUTS, *BOOTSTRAP_INPUTS)))
LEGACY_TARGET_INPUTS = (
    "Include/opcode.h",
    "Include/object.h",
    "Include/ceval.h",
    "Include/internal/pycore_opcode_utils.h",
    "Include/internal/pycore_intrinsics.h",
    "Include/cpython/code.h",
    "Include/internal/pycore_code.h",
    "Include/internal/pycore_global_strings.h",
    "Include/internal/pycore_global_objects.h",
    "Include/patchlevel.h",
    "Python/compile.c",
    "Python/flowgraph.c",
    "Python/assemble.c",
    "Python/Python-ast.c",
    "Lib/importlib/_bootstrap_external.py",
)
MARSHAL_INPUTS = (
    "Include/marshal.h",
    "Python/marshal.c",
)
# These mortal strings enter the intern table during isolated CPython startup, before the
# compatibility oracle calls compile(). They are not part of the pinned static metadata.
STARTUP_INTERNED_STRINGS = (
    "500",
    "MISSING",
    "None",
    "ascii",
    "cache",
    "cached",
    "candidate",
    "darwin",
    "date",
    "error",
    "eval",
    "kwargs",
    "l1",
    "l2",
    "link",
    "map",
    "min",
    "missing",
    "nan",
    "new",
    "old_value",
    "other",
    "output",
    "package",
    "python",
    "quiet",
    "remove",
    "root",
    "run",
    "sum",
    "system",
    "test",
    "timestamp",
    "u7",
    "unknown",
    "update",
    "user",
    "var",
    "warn",
    "win32",
)
# signal.pause is initialized only when CPython is built with HAVE_PAUSE.
UNIX_STARTUP_INTERNED_STRINGS = ("pause",)

CRATE_ROOT = Path(__file__).resolve().parents[1]
OUTPUT = CRATE_ROOT / "src" / "target" / "cpython_3_14_5.rs"
MARSHAL_OUTPUT = CRATE_ROOT / "src" / "marshal" / "v5.rs"
STARTUP_314_INPUT = "scripts/target_metadata/cpython_3_14_5_startup.json"
STARTUP_314_SHA256 = "2f4c1896da530468f57bd870ae893498da6e84b93c93dabfe773a1c4bd828bc5"
STARTUP_315_INPUT = "scripts/target_metadata/cpython_3_15_0rc2_startup.json"
STARTUP_315_SHA256 = "57c1d606a70991d3034184aae59352d3f3810194785b76a7e16b9adb9d066d63"
LEGACY_STARTUP_INPUTS = {
    "3.12": (
        "scripts/target_metadata/cpython_3_12_14_startup.json",
        "5b019188909c2400637475650fb3d9f4f6b891c9c701a484be0bf989d1e8e44b",
    ),
    "3.13": (
        "scripts/target_metadata/cpython_3_13_15_startup.json",
        "8304f6b6c8a3b1004ca1423686d2e856ec0309c3133ea91772daca87eb061124",
    ),
}
V4_INPUT_DIGESTS = {
    "3.12": {
        "Include/marshal.h": "d7f5760ef6496776cee99aca5491789f6ab261a78b156b5758538ea15e1827e5",
        "Python/marshal.c": "6d2dc841001316ed7f9255ec03aeeb6e14780421f44ba61436da638c6f49bf0c",
    },
    "3.13": {
        "Include/marshal.h": "d7f5760ef6496776cee99aca5491789f6ab261a78b156b5758538ea15e1827e5",
        "Python/marshal.c": "e82da48b37ce030f2fa5c6996b1636d1f6b5082a2448b5b6f76188b470b38fe2",
    },
}


def read_bootstrap_strings(sources: dict[str, str]) -> tuple[str, ...]:
    """Verify the source-derived Linux supplement without compiling on the host."""
    data = (CRATE_ROOT / BOOTSTRAP_314_INPUT).read_bytes()
    if hashlib.sha256(data).hexdigest() != BOOTSTRAP_314_SHA256:
        raise ValueError("pinned Python 3.14 bootstrap checksum mismatch")
    profile = json.loads(data)
    if (
        profile["target_tag"] != TARGET_TAG
        or profile["target_commit"] != TARGET_COMMIT
        or profile["platform"] != "linux"
    ):
        raise ValueError("bootstrap profile does not match the selected target")
    helper = CRATE_ROOT / "scripts/generate_cpython_bootstrap.py"
    if hashlib.sha256(helper.read_bytes()).hexdigest() != profile["generator_sha256"]:
        raise ValueError("bootstrap generator changed; regenerate its fixture")
    expected = {
        relative: hashlib.sha256(sources[relative].encode()).hexdigest()
        for relative in BOOTSTRAP_INPUTS
    }
    if profile["input_sha256"] != expected:
        raise ValueError("bootstrap profile does not match the pinned source inputs")
    values = profile["strings"]
    if values != sorted(set(values)) or len(values) != profile["supplemental_entries"]:
        raise ValueError("bootstrap strings are not unique, sorted and complete")
    if any(not isinstance(value, str) or value.startswith("/") for value in values):
        raise ValueError("bootstrap profile contains an environment-specific path")
    return tuple(values)


def startup_input() -> tuple[str, str]:
    if TARGET_MINOR == "3.14":
        return STARTUP_314_INPUT, STARTUP_314_SHA256
    if TARGET_MINOR == "3.15":
        return STARTUP_315_INPUT, STARTUP_315_SHA256
    if TARGET_MINOR not in LEGACY_STARTUP_INPUTS:
        raise ValueError(
            f"verified startup supplement is not available for {TARGET_MINOR}"
        )
    return LEGACY_STARTUP_INPUTS[TARGET_MINOR]


def read_startup_strings() -> tuple[str, ...]:
    """Read the verified neutral Linux startup supplement for the selected target."""
    relative, digest = startup_input()
    data = (CRATE_ROOT / relative).read_bytes()
    if hashlib.sha256(data).hexdigest() != digest:
        raise ValueError(
            f"pinned Python {TARGET_MINOR} startup profile checksum mismatch"
        )
    profile = json.loads(data)
    if profile["target_tag"] != TARGET_TAG or profile["target_commit"] != TARGET_COMMIT:
        raise ValueError("startup profile does not match the selected CPython target")
    values = profile["strings"]
    if values != sorted(set(values)) or len(values) != profile["supplemental_entries"]:
        raise ValueError("startup profile strings are not unique, sorted and complete")
    if any(not isinstance(value, str) or value.startswith("/") for value in values):
        raise ValueError("startup profile contains an environment-specific path")
    validate_minimal_startup_profile(
        profile,
        (CRATE_ROOT.parent.parent / "scripts/cpython-reference.c").read_bytes(),
    )
    if TARGET_MINOR == "3.14":
        retention = profile["retention"]
        owners = retention["mortal_owners"]
        mortal = retention["mortal_dynamic_entries"]
        if (
            profile["platform"] != "linux"
            or profile["architecture"] != "x86_64"
            or not profile["gil_enabled"]
            or not profile["isolated"]
            or profile["site_enabled"]
            or retention["proved_mortal_entries"] != mortal
            or len(owners) != mortal
            or list(owners) != sorted(owners)
            or any(not isinstance(owner, str) or not owner for owner in owners.values())
            or retention["static_entries"]
            + retention["immortal_dynamic_entries"]
            + mortal
            != profile["canonical_snapshot_entries"]
        ):
            raise ValueError(
                "Python 3.14 startup profile has incomplete retained ownership"
            )
        provenance_path = (
            CRATE_ROOT / "scripts/target_metadata/cpython_3_14_5_startup_ownership.json"
        )
        provenance_data = provenance_path.read_bytes()
        provenance = json.loads(provenance_data)
        auditor = (CRATE_ROOT / "scripts/audit_startup_owners.py").read_bytes()
        layout_generator = (
            CRATE_ROOT / "scripts/generate_startup_owner_layout.py"
        ).read_bytes()
        if (
            hashlib.sha256(provenance_data).hexdigest()
            != retention["owner_layout_provenance_sha256"]
            or provenance["source_commit"] != TARGET_COMMIT
            or provenance["layout_sha256"] != retention["owner_layout_sha256"]
            or hashlib.sha256(layout_generator).hexdigest()
            != provenance["generator_sha256"]
            or hashlib.sha256(auditor).hexdigest() != retention["audit_script_sha256"]
        ):
            raise ValueError(
                "Python 3.14 startup ownership provenance checksum mismatch"
            )
    return tuple(values)


def validate_minimal_startup_profile(profile: dict, reference_source: bytes) -> None:
    """Bind native startup data to the reference and independent capture receipts."""
    observations = profile.get("observations", [])
    if (
        profile.get("schema_version") != 2
        or profile.get("reference_protocol") != "minimal-v2"
        or profile.get("reference_source_sha256")
        != hashlib.sha256(reference_source).hexdigest()
        or profile.get("platform") != "linux"
        or profile.get("architecture") != "x86_64"
        or profile.get("gil_enabled") is not True
        or profile.get("isolated") is not True
        or profile.get("site_enabled") is not False
        or len(observations) != 2
        or len({row.get("receipt_sha256") for row in observations}) != 2
        or any(
            row.get("actual_exit") != 0
            or row.get("thread_count") != 1
            or row.get("two_complete_reads_equal") is not True
            or row.get("observed_equals_unobserved") is not True
            or row.get("canonical_sha256") != profile["canonical_snapshot_sha256"]
            or row.get("entries") != profile["canonical_snapshot_entries"]
            for row in observations
        )
    ):
        raise ValueError("minimal reference startup provenance is incomplete")


def select_target_version(version: str) -> None:
    """Select an exact, supported release without changing the default target."""
    global TARGET_MINOR, TARGET_TAG, TARGET_COMMIT, TARGET_VERSION
    global TARGET_INPUTS, MARSHAL_INPUTS, OUTPUT, MARSHAL_OUTPUT
    TARGET_MINOR = version
    TARGET_TAG, TARGET_COMMIT, TARGET_VERSION, marshal_version = TARGETS[version]
    TARGET_INPUTS = MODERN_TARGET_INPUTS
    if version == "3.14":
        TARGET_INPUTS = tuple(dict.fromkeys((*TARGET_INPUTS, *BOOTSTRAP_INPUTS)))
    if version == "3.12":
        TARGET_INPUTS = (
            *LEGACY_TARGET_INPUTS,
            "Include/internal/pycore_opcode.h",
            "Python/opcode_metadata.h",
            "Lib/opcode.py",
        )
    elif version == "3.13":
        TARGET_INPUTS = (
            *LEGACY_TARGET_INPUTS,
            "Include/opcode_ids.h",
            "Include/internal/pycore_opcode_metadata.h",
            "Lib/_opcode_metadata.py",
        )
    if version == "3.15":
        TARGET_INPUTS += (
            "Python/assemble.c",
            "Include/internal/pycore_runtime_structs.h",
        )
    marshal_header = (
        "Include/cpython/marshal.h" if version == "3.15" else "Include/marshal.h"
    )
    MARSHAL_INPUTS = (marshal_header, "Python/marshal.c")
    module = TARGET_TAG.removeprefix("v").replace(".", "_")
    OUTPUT = CRATE_ROOT / "src" / "target" / f"cpython_{module}.rs"
    MARSHAL_OUTPUT = CRATE_ROOT / "src" / "marshal" / f"v{marshal_version}.rs"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--cpython",
        type=Path,
        required=True,
        help="path to a CPython checkout at the pinned commit",
    )
    parser.add_argument(
        "--target-version",
        choices=TARGETS,
        default="3.14",
        help="Python minor version; each choice resolves to an exact pinned release",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail instead of writing if the checked-in module is stale",
    )
    return parser.parse_args()


def require_match(pattern: str, source: str, description: str) -> re.Match[str]:
    match = re.search(pattern, source, re.MULTILINE)
    if match is None:
        raise ValueError(f"failed to find {description}")
    return match


def git_output(checkout: Path, *arguments: str) -> str:
    return subprocess.run(
        ["git", "-C", str(checkout), *arguments],
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout.strip()


def verify_checkout(checkout: Path) -> None:
    commit = git_output(checkout, "rev-parse", "HEAD^{commit}")
    if commit != TARGET_COMMIT:
        raise ValueError(
            f"CPython checkout is at {commit}, expected {TARGET_COMMIT} ({TARGET_TAG})"
        )
    try:
        tag_commit = git_output(checkout, "rev-parse", f"{TARGET_TAG}^{{commit}}")
    except subprocess.CalledProcessError:
        return
    if tag_commit != TARGET_COMMIT:
        raise ValueError(
            f"{TARGET_TAG} resolves to {tag_commit}, expected {TARGET_COMMIT}"
        )


def read_committed_file(checkout: Path, relative: str) -> str:
    """Read an input from the pinned commit, ignoring working-tree changes."""
    try:
        result = subprocess.run(
            ["git", "-C", str(checkout), "show", f"{TARGET_COMMIT}:{relative}"],
            check=True,
            capture_output=True,
        )
    except subprocess.CalledProcessError as error:
        detail = error.stderr.decode(errors="replace").strip()
        message = f"failed to read {relative} from CPython commit {TARGET_COMMIT}"
        if detail:
            message = f"{message}: {detail}"
        raise ValueError(message) from error
    try:
        return result.stdout.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(
            f"CPython input {relative} at {TARGET_COMMIT} is not UTF-8"
        ) from error


def read_inputs(checkout: Path) -> dict[str, str]:
    return {
        relative: read_committed_file(checkout, relative)
        for relative in TARGET_INPUTS + MARSHAL_INPUTS
    }


def parse_preinterned_strings(source: str) -> list[str]:
    strings = set(
        re.findall(r"(?m)^[ \t]*STRUCT_FOR_ID\(([A-Za-z_][A-Za-z0-9_]*)\)", source)
    )
    literal_tokens = re.findall(
        r'STRUCT_FOR_STR\([^,]+,\s*("(?:\\.|[^"\\])*")\)',
        source,
    )
    try:
        strings.update(ast.literal_eval(token) for token in literal_tokens)
    except (SyntaxError, ValueError) as error:
        raise ValueError("invalid static string literal") from error
    required = {"", "<module>", "sort"}
    if not required.issubset(strings):
        raise ValueError("pre-interned string table is incomplete")
    return sorted(strings)


def parse_compiler_interned_strings(source: str) -> list[str]:
    """Read names interned when builtin compile() initializes the AST types."""
    identifiers = require_match(
        r"static int init_identifiers\(struct ast_state \*state\)\s*\{([\s\S]*?)\n\}",
        source,
        "AST identifier initialization",
    ).group(1)
    literal_tokens = re.findall(
        r'PyUnicode_InternFromString\(("(?:\\.|[^"\\])*")\)', identifiers
    )
    try:
        strings = {ast.literal_eval(token) for token in literal_tokens}
    except (SyntaxError, ValueError) as error:
        raise ValueError("invalid AST identifier literal") from error
    if not {"body", "left", "right"}.issubset(strings):
        raise ValueError("compiler-interned string table is incomplete")
    return sorted(strings)


def rust_string_literal(value: str) -> str:
    escaped = []
    for character in value:
        match character:
            case "\\":
                escaped.append("\\\\")
            case '"':
                escaped.append('\\"')
            case "\0":
                escaped.append("\\0")
            case "\n":
                escaped.append("\\n")
            case "\r":
                escaped.append("\\r")
            case "\t":
                escaped.append("\\t")
            case _ if ord(character) < 0x20 or ord(character) == 0x7F:
                escaped.append(f"\\x{ord(character):02x}")
            case _:
                escaped.append(character)
    return f'"{"".join(escaped)}"'


def render_compact_rust_strings(values: list[str]) -> list[str]:
    lines = []
    row = "    "
    for value in values:
        literal = rust_string_literal(value) + ","
        if row.strip() and len(row) + len(literal) > 100:
            lines.append(row.rstrip())
            row = "    "
        row += literal + " "
    if row.strip():
        lines.append(row.rstrip())
    return lines


def render_preinterned_lookup(
    preinterned_strings: list[str],
    startup_strings: tuple[str, ...],
    compiler_strings: tuple[str, ...] = (),
    *,
    compiler_strings_on_linux: bool = True,
) -> list[str]:
    def prefix(value: str) -> int:
        encoded = value.encode()
        return (encoded[0] << 8) | (encoded[1] if len(encoded) > 1 else 0)

    ranges: dict[int, tuple[int, int]] = {}
    for index, value in enumerate(preinterned_strings):
        if not value:
            continue
        key = prefix(value)
        if key in ranges:
            start, end = ranges[key]
            if end != index:
                raise ValueError("preinterned prefix ranges are not contiguous")
            ranges[key] = (start, index + 1)
        else:
            ranges[key] = (index, index + 1)

    supplemental: dict[int, list[str]] = {}
    supplemental_strings = sorted(set(startup_strings) | set(compiler_strings))
    for value in supplemental_strings:
        if value and value not in preinterned_strings:
            supplemental.setdefault(prefix(value), []).append(value)

    empty = str("" in preinterned_strings or "" in supplemental_strings).lower()
    if (
        not compiler_strings_on_linux
        and "" in compiler_strings
        and "" not in preinterned_strings
        and "" not in startup_strings
    ):
        empty = 'cfg!(not(target_os = "linux"))'
    lines = [
        "pub(crate) fn is_preinterned_string(value: &str) -> bool {",
        "    let prefix = match value.as_bytes() {",
        f"        [] => return {empty},",
        "        [first] => u16::from(*first) << 8,",
        "        [first, second, ..] => u16::from_be_bytes([*first, *second]),",
        "    };",
        "    let candidates: &[&str] = match prefix {",
    ]
    for key in sorted(ranges.keys() | supplemental.keys()):
        candidates = supplemental.get(key, [])
        conditions = []
        for value in candidates:
            condition = f"value == {rust_string_literal(value)}"
            if value in UNIX_STARTUP_INTERNED_STRINGS:
                condition = f"(cfg!(unix) && {condition})"
            if (
                not compiler_strings_on_linux
                and value in compiler_strings
                and value not in startup_strings
            ):
                condition = f'cfg!(not(target_os = "linux")) && {condition}'
            conditions.append(condition)
        condition = " || ".join(conditions)
        if key not in ranges:
            lines.append(f"        0x{key:04x} => return {condition},")
            continue
        start, end = ranges[key]
        # Emit each bucket as a constant slice so equal buckets can be merged across targets.
        bucket = ", ".join(
            rust_string_literal(value) for value in preinterned_strings[start:end]
        )
        if not candidates:
            lines.append(f"        0x{key:04x} => &[{bucket}],")
            continue
        lines.extend(
            [
                f"        0x{key:04x} => {{",
                f"            if {condition} {{",
                "                return true;",
                "            }",
                f"            &[{bucket}]",
                "        }",
            ]
        )
    lines.extend(
        [
            "        _ => return false,",
            "    };",
            "    candidates.binary_search(&value).is_ok()",
            "}",
        ]
    )
    return lines


def parse_opcodes(source: str) -> list[tuple[str, int]]:
    section = source.split("/* Instruction opcodes for compiled code */", 1)[1]
    section = section.split("#define HAVE_ARGUMENT", 1)[0]
    minimum_specialized = int(
        require_match(
            r"^#define\s+MIN_SPECIALIZED_OPCODE\s+(\d+)\s*$",
            source,
            "first specialized opcode",
        ).group(1)
    )
    opcodes = []
    ids = set()
    for name, value in re.findall(
        r"^#define\s+([A-Z][A-Z0-9_]*)\s+(\d+)\s*$", section, re.MULTILINE
    ):
        code = int(value)
        if code >= minimum_specialized:
            continue
        if code in ids:
            raise ValueError(f"duplicate physical opcode ID {code}")
        ids.add(code)
        opcodes.append((name, code))
    if not opcodes or "RESUME" not in dict(opcodes):
        raise ValueError(
            "opcode table does not contain the expected RESUME instruction"
        )
    return opcodes


def parse_caches(source: str) -> dict[str, int]:
    section = source.split("const uint8_t _PyOpcode_Caches[256] = {", 1)[1]
    section = section.split("};", 1)[0]
    return {
        name: int(value)
        for name, value in re.findall(
            r"^\s*\[([A-Z][A-Z0-9_]*)\]\s*=\s*(\d+),\s*$",
            section,
            re.MULTILINE,
        )
    }


def parse_opcode_flags(source: str) -> dict[str, set[str]]:
    section = require_match(
        r"const struct opcode_metadata _PyOpcode_opcode_metadata\[\d+\] = \{([\s\S]*?)\};",
        source,
        "opcode metadata table",
    ).group(1)
    flags = {}
    for name, expression in re.findall(
        r"^\s*\[([A-Z][A-Z0-9_]*)\]\s*=\s*"
        r"\{\s*true,\s*[^,]+,\s*([^}]+)\},\s*$",
        section,
        re.MULTILINE,
    ):
        flags[name] = set(re.findall(r"HAS_[A-Z_]+_FLAG", expression))
    if not flags:
        raise ValueError("no opcode flags found")
    return flags


def parse_opcode_predicate(source: str, macro: str) -> set[str]:
    lines = source.splitlines()
    for index, line in enumerate(lines):
        if not line.startswith(f"#define {macro}(opcode)"):
            continue
        body = [line]
        while body[-1].rstrip().endswith("\\"):
            index += 1
            body.append(lines[index])
        opcodes = set(
            re.findall(r"\(opcode\)\s*==\s*([A-Z][A-Z0-9_]*)", "\n".join(body))
        )
        if not opcodes:
            raise ValueError(f"opcode predicate {macro} is empty")
        return opcodes
    raise ValueError(f"failed to find opcode predicate {macro}")


def parse_stack_function(source: str, direction: str) -> dict[str, str]:
    start = f"int _PyOpcode_num_{direction}(int opcode, int oparg)  {{"
    section = source.split(start, 1)[1].split("#endif", 1)[0]
    effects = {
        name: " ".join(expression.split())
        for name, expression in re.findall(
            r"case\s+([A-Z][A-Z0-9_]*):\s*return\s+([^;]+);", section
        )
    }
    if not effects:
        raise ValueError(f"no {direction} stack effects found")
    return effects


def rust_stack_expression(expression: str) -> str:
    allowed = re.fullmatch(r"[0-9A-Fa-fxXoparg +\-*&>()]+", expression)
    if allowed is None:
        raise ValueError(f"unsupported stack-effect expression: {expression}")
    return re.sub(r"\boparg\b", "argument", expression).replace("0xFF", "0xff")


def format_rust(source: str) -> str:
    """Format generated Rust with the workspace toolchain before comparing it."""
    return subprocess.run(
        ["rustfmt", "--edition", "2024", "--emit", "stdout"],
        input=source,
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout


def parse_numeric_defines(source: str, prefix: str) -> list[tuple[str, int]]:
    definitions = []
    for name, hexadecimal, decimal in re.findall(
        rf"^#define\s+({prefix}[A-Z0-9_]*)\s+\(?(?:(0x[0-9A-Fa-f]+)|(\d+))\)?(?:\s|/|$)",
        source,
        re.MULTILINE,
    ):
        value = int(hexadecimal or decimal, 0)
        definitions.append((name, value))
    return definitions


def require_definitions(
    definitions: list[tuple[str, int]], required: set[str], description: str
) -> dict[str, int]:
    values = dict(definitions)
    missing = required - values.keys()
    if missing:
        raise ValueError(f"{description} is missing {sorted(missing)}")
    return values


def render_operand_type(
    lines: list[str], type_name: str, definitions: list[tuple[str, int]], prefix: str
) -> None:
    lines.extend(
        [
            "    #[derive(Clone, Copy, Debug, Eq, PartialEq)]",
            f"    pub(crate) struct {type_name}(u32);",
            "",
            "    #[allow(dead_code)]",
            f"    impl {type_name} {{",
        ]
    )
    for name, value in definitions:
        associated_name = name.removeprefix(prefix)
        lines.append(
            f"        pub(crate) const {associated_name}: Self = Self({value});"
        )
    lines.extend(
        [
            "",
            "        pub(crate) const fn argument(self) -> u32 {",
            "            self.0",
            "        }",
            "    }",
            "",
        ]
    )


def parse_import_modes(source: str) -> tuple[int, list[tuple[str, int]]]:
    """Extract ordinary, explicit lazy and forced eager import operands."""
    call = r"ADDOP_NAME_CUSTOM\([^;\n]*IMPORT_NAME,[^;\n]*, names, (\d+), (\d+)\);"
    patterns = (
        ("LAZY", r"if \(s->v.Import.is_lazy\) \{[\s\S]*?"),
        ("EAGER", r"// force eager import in try/except block\s*"),
        ("DEFAULT", r"\} else \{\s*"),
    )
    definitions = []
    shifts = set()
    for name, prefix in patterns:
        match = require_match(prefix + call, source, f"{name.lower()} import operand")
        shift, value = map(int, match.groups())
        shifts.add(shift)
        definitions.append((name, value))
    if len(shifts) != 1:
        raise ValueError("import modes disagree on the name index shift")
    shift = shifts.pop()
    if not 0 < shift < 32 or any(value >= 1 << shift for _, value in definitions):
        raise ValueError("invalid import operand layout")
    if len({value for _, value in definitions}) != len(definitions):
        raise ValueError("import modes do not have distinct operands")
    return shift, definitions


def opcode_match_expression(opcodes: list[tuple[str, int]], names: set[str]) -> str:
    variants = [f"opcodes::{name}" for name, _ in opcodes if name in names]
    if not variants:
        return "false"
    return "matches!(opcode, " + " | ".join(variants) + ")"


def parse_character_defines(source: str, prefix: str) -> list[tuple[str, int]]:
    definitions = []
    for name, literal in re.findall(
        rf"^#define\s+({prefix}[A-Z0-9_]*)\s+'([^']+)'",
        source,
        re.MULTILINE,
    ):
        value = ast.literal_eval(f"'{literal}'")
        if not isinstance(value, str) or len(value) != 1:
            raise ValueError(f"unsupported character literal for {name}: {literal}")
        definitions.append((name, ord(value)))
    return definitions


def rust_hex(value: int, digits: int) -> str:
    """Format a Rust hexadecimal literal with four-digit separators."""
    hexadecimal = f"{value:0{digits}x}"
    first_group = len(hexadecimal) % 4 or 4
    groups = [hexadecimal[:first_group]]
    groups.extend(
        hexadecimal[index : index + 4]
        for index in range(first_group, len(hexadecimal), 4)
    )
    return "0x" + "_".join(groups)


def rust_byte(value: int) -> str:
    if 0x20 <= value <= 0x7E:
        character = chr(value).replace("\\", "\\\\").replace("'", "\\'")
        return f"b'{character}'"
    return rust_hex(value, 2)


def render(sources: dict[str, str]) -> str:
    if TARGET_MINOR in {"3.12", "3.13"}:
        from generate_legacy_target import render_legacy_target

        return render_legacy_target(sources, SimpleNamespace(**globals()))
    opcode_ids = sources["Include/opcode_ids.h"]
    opcode_header = sources["Include/opcode.h"]
    object_header = sources["Include/object.h"]
    ceval_header = sources["Include/ceval.h"]
    metadata = sources["Include/internal/pycore_opcode_metadata.h"]
    opcode_utils = sources["Include/internal/pycore_opcode_utils.h"]
    intrinsics_header = sources["Include/internal/pycore_intrinsics.h"]
    ceval_internal = sources["Include/internal/pycore_ceval.h"]
    code_header = sources["Include/cpython/code.h"]
    local_header = sources["Include/internal/pycore_code.h"]
    magic_header = sources["Include/internal/pycore_magic_number.h"]
    global_strings = sources["Include/internal/pycore_global_strings.h"]
    patchlevel = sources["Include/patchlevel.h"]
    codegen = sources["Python/codegen.c"]
    flowgraph = sources["Python/flowgraph.c"]

    preinterned_strings = parse_preinterned_strings(global_strings)
    compiler_interned_strings = parse_compiler_interned_strings(
        sources["Python/Python-ast.c"]
    )
    opcodes = parse_opcodes(opcode_ids)
    opcode_names = {name for name, _ in opcodes}
    caches = parse_caches(metadata)
    opcode_flags = parse_opcode_flags(metadata)
    popped = parse_stack_function(metadata, "popped")
    pushed = parse_stack_function(metadata, "pushed")
    for name in opcode_names:
        if name not in popped or name not in pushed:
            raise ValueError(f"missing stack metadata for {name}")
        if name not in opcode_flags:
            raise ValueError(f"missing opcode flags for {name}")
    unknown_caches = set(caches) - {
        name
        for name, value in re.findall(
            r"^#define\s+([A-Z][A-Z0-9_]*)\s+(\d+)\s*$", opcode_ids, re.MULTILINE
        )
        if int(value) < 256
    }
    if unknown_caches:
        raise ValueError(
            f"cache metadata references unknown opcodes: {sorted(unknown_caches)}"
        )

    predicates = {
        rust_name: parse_opcode_predicate(opcode_utils, cpython_name) & opcode_names
        for rust_name, cpython_name in (
            ("is_scope_exit", "IS_SCOPE_EXIT_OPCODE"),
            ("is_unconditional_jump", "IS_UNCONDITIONAL_JUMP_OPCODE"),
            ("is_conditional_jump", "IS_CONDITIONAL_JUMP_OPCODE"),
        )
    }
    if any(not names for names in predicates.values()):
        raise ValueError(
            "generated opcode predicate is empty after removing pseudo-instructions"
        )

    unary_intrinsics_source = intrinsics_header.split("/* Unary Functions: */", 1)[
        1
    ].split("MAX_INTRINSIC_1", 1)[0]
    binary_intrinsics_source = intrinsics_header.split("/* Binary Functions: */", 1)[
        1
    ].split("MAX_INTRINSIC_2", 1)[0]
    unary_intrinsics = [
        definition
        for definition in parse_numeric_defines(unary_intrinsics_source, "INTRINSIC_")
        if definition[0] != "INTRINSIC_1_INVALID"
    ]
    binary_intrinsics = [
        definition
        for definition in parse_numeric_defines(binary_intrinsics_source, "INTRINSIC_")
        if definition[0] != "INTRINSIC_2_INVALID"
    ]
    require_definitions(
        unary_intrinsics,
        {"INTRINSIC_PRINT", "INTRINSIC_TYPEALIAS"},
        "unary-intrinsic table",
    )
    require_definitions(
        binary_intrinsics,
        {"INTRINSIC_PREP_RERAISE_STAR", "INTRINSIC_SET_TYPEPARAM_DEFAULT"},
        "binary-intrinsic table",
    )

    function_attributes = parse_numeric_defines(opcode_utils, "MAKE_FUNCTION_")
    common_constants = parse_numeric_defines(opcode_utils, "CONSTANT_")
    resume_definitions = parse_numeric_defines(opcode_utils, "RESUME_")
    resume_locations = [
        definition
        for definition in resume_definitions
        if not definition[0].endswith("_MASK")
    ]
    resume_values = require_definitions(
        resume_definitions,
        {"RESUME_OPARG_LOCATION_MASK", "RESUME_OPARG_DEPTH1_MASK"},
        "RESUME operand table",
    )
    require_definitions(
        function_attributes,
        {
            "MAKE_FUNCTION_DEFAULTS",
            "MAKE_FUNCTION_KWDEFAULTS",
            "MAKE_FUNCTION_ANNOTATIONS",
            "MAKE_FUNCTION_CLOSURE",
            "MAKE_FUNCTION_ANNOTATE",
        },
        "function-attribute table",
    )
    require_definitions(
        common_constants,
        {
            "CONSTANT_ASSERTIONERROR",
            "CONSTANT_NOTIMPLEMENTEDERROR",
            "CONSTANT_BUILTIN_TUPLE",
            "CONSTANT_BUILTIN_ALL",
            "CONSTANT_BUILTIN_ANY",
        },
        "common-constant table",
    )

    binary_operations = [
        definition
        for definition in parse_numeric_defines(opcode_header, "NB_")
        if definition[0] != "NB_OPARG_LAST"
    ]
    require_definitions(
        binary_operations,
        {"NB_ADD", "NB_INPLACE_XOR", "NB_SUBSCR"},
        "binary-operation table",
    )

    rich_comparisons = require_definitions(
        parse_numeric_defines(object_header, "Py_"),
        {"Py_LT", "Py_LE", "Py_EQ", "Py_NE", "Py_GT", "Py_GE"},
        "rich-comparison table",
    )
    comparison_masks = require_definitions(
        parse_numeric_defines(local_header, "COMPARISON_"),
        {
            "COMPARISON_UNORDERED",
            "COMPARISON_LESS_THAN",
            "COMPARISON_GREATER_THAN",
            "COMPARISON_EQUALS",
        },
        "comparison-mask table",
    )
    comparison_shift = int(
        require_match(
            r"ADDOP_I\(c, loc, COMPARE_OP, \(cmp << (\d+)\) \| compare_masks\[cmp\]\);",
            codegen,
            "COMPARE_OP operator shift",
        ).group(1)
    )
    comparison_boolean_mask = int(
        require_match(
            r"INSTR_SET_OP1\([^\n]+COMPARE_OP, oparg \| (\d+)\);",
            flowgraph,
            "COMPARE_OP boolean mask",
        ).group(1)
    )
    comparison_masks["COMPARISON_NOT_EQUALS"] = (
        comparison_masks["COMPARISON_UNORDERED"]
        | comparison_masks["COMPARISON_LESS_THAN"]
        | comparison_masks["COMPARISON_GREATER_THAN"]
    )
    comparison_operations = [
        (
            name,
            (rich_comparisons[f"Py_{name}"] << comparison_shift) | mask,
        )
        for name, mask in (
            ("LT", comparison_masks["COMPARISON_LESS_THAN"]),
            (
                "LE",
                comparison_masks["COMPARISON_LESS_THAN"]
                | comparison_masks["COMPARISON_EQUALS"],
            ),
            ("EQ", comparison_masks["COMPARISON_EQUALS"]),
            ("NE", comparison_masks["COMPARISON_NOT_EQUALS"]),
            ("GT", comparison_masks["COMPARISON_GREATER_THAN"]),
            (
                "GE",
                comparison_masks["COMPARISON_GREATER_THAN"]
                | comparison_masks["COMPARISON_EQUALS"],
            ),
        )
    ]

    conversions = [
        definition
        for definition in parse_numeric_defines(ceval_header, "FVC_")
        if definition[0] != "FVC_MASK"
    ]
    special_methods = [
        definition
        for definition in parse_numeric_defines(ceval_internal, "SPECIAL_")
        if definition[0] != "SPECIAL_MAX"
    ]
    require_definitions(
        conversions,
        {"FVC_NONE", "FVC_STR", "FVC_REPR", "FVC_ASCII"},
        "conversion table",
    )
    require_definitions(
        special_methods,
        {
            "SPECIAL___ENTER__",
            "SPECIAL___EXIT__",
            "SPECIAL___AENTER__",
            "SPECIAL___AEXIT__",
        },
        "special-method table",
    )

    version = tuple(
        int(
            require_match(
                rf"^#define\s+PY_{part}_VERSION\s+(\d+)$", patchlevel, part
            ).group(1)
        )
        for part in ("MAJOR", "MINOR", "MICRO")
    )
    if version != TARGET_VERSION:
        raise ValueError(f"unexpected CPython version {version}")
    magic = int(
        require_match(
            r"^#define\s+PYC_MAGIC_NUMBER\s+(\d+)$", magic_header, "magic number"
        ).group(1)
    )
    magic_bytes = (magic & 0xFF, magic >> 8, 0x0D, 0x0A)

    code_flags = [
        item
        for item in parse_numeric_defines(code_header, "CO_")
        if item[0] != "CO_MAXBLOCKS"
    ]
    local_kinds = parse_numeric_defines(local_header, "CO_FAST_")
    required_flags = {"CO_OPTIMIZED", "CO_METHOD", "CO_FUTURE_ANNOTATIONS"}
    if not required_flags.issubset({name for name, _ in code_flags}):
        raise ValueError("code-flag table is incomplete")
    required_kinds = {"CO_FAST_ARG_POS", "CO_FAST_LOCAL", "CO_FAST_FREE"}
    if not required_kinds.issubset({name for name, _ in local_kinds}):
        raise ValueError("local-kind table is incomplete")

    lines = [
        "// @generated by scripts/generate_cpython_target.py; do not edit.",
        f"// CPython {TARGET_TAG} ({TARGET_COMMIT}).",
    ]
    for relative in TARGET_INPUTS:
        digest = hashlib.sha256(sources[relative].encode()).hexdigest()
        lines.append(f"// {relative}: sha256:{digest}")
    if TARGET_MINOR == "3.14":
        lines.append(f"// {BOOTSTRAP_314_INPUT}: sha256:{BOOTSTRAP_314_SHA256}")
        lines.append(f"// {STARTUP_314_INPUT}: sha256:{STARTUP_314_SHA256}")
    elif TARGET_MINOR == "3.15":
        lines.append(f"// {STARTUP_315_INPUT}: sha256:{STARTUP_315_SHA256}")
    lines.extend(
        [
            "",
            "use super::Opcode;"
            if TARGET_MINOR == "3.14"
            else "use super::{Opcode, opcodes};",
            "",
            f'pub(crate) const TARGET_TAG: &str = "{TARGET_TAG}";',
            f'pub(crate) const TARGET_COMMIT: &str = "{TARGET_COMMIT}";',
            'pub(crate) const TARGET_IMPLEMENTATION: &str = "cpython";',
            f"pub(crate) const TARGET_VERSION: (u8, u8, u8) = ({version[0]}, {version[1]}, {version[2]});",
            "pub(crate) const TARGET_MAGIC_NUMBER: [u8; 4] = "
            f"[0x{magic_bytes[0]:02x}, 0x{magic_bytes[1]:02x}, 0x{magic_bytes[2]:02x}, 0x{magic_bytes[3]:02x}];",
            "",
        ]
    )
    if TARGET_MINOR == "3.14":
        lines.extend(["pub(crate) mod opcodes {", "    use super::Opcode;", ""])
        for name, code in opcodes:
            lines.append(f"    pub(crate) const {name}: Opcode = Opcode::new({code});")
        lines.extend(
            [
                "}",
                "",
                "impl Opcode {",
                "    /// Returns the inline-cache width generated from the pinned opcode metadata.",
                "    pub(crate) const fn caches(self) -> u8 {",
                "        match self {",
            ]
        )
    else:
        # The IR keeps semantic identities from the original target. Only the
        # encoding boundary translates them to the selected target's IDs.
        semantic_names = parse_opcodes_from_generated_names(
            CRATE_ROOT / "src" / "target" / "cpython_3_14_5.rs"
        )
        missing = opcode_names - semantic_names
        if missing:
            raise ValueError(f"target requires new semantic opcodes: {sorted(missing)}")
        lines.extend(
            ["pub(crate) const fn code(opcode: Opcode) -> u8 {", "    match opcode {"]
        )
        for name, code in opcodes:
            lines.append(f"        opcodes::{name} => {code},")
        lines.append(
            f"        opcodes::GET_YIELD_FROM_ITER => {dict(opcodes)['GET_ITER']},"
        )
        lines.extend(
            [
                '        _ => panic!("unsupported opcode for CPython 3.15"),',
                "    }",
                "}",
                "",
            ]
        )
        lines.extend(
            ["pub(crate) const fn caches(opcode: Opcode) -> u8 {", "    match opcode {"]
        )
    for name, _ in opcodes:
        if width := caches.get(name, 0):
            lines.append(f"            opcodes::{name} => {width},")
    if TARGET_MINOR == "3.14":
        lines.extend(["            _ => 0,", "        }", "    }", "}", ""])
    else:
        lines.append(f"        opcodes::GET_YIELD_FROM_ITER => {caches['GET_ITER']},")
        lines.extend(["        _ => 0,", "    }", "}", ""])
        end_send_offset = int(
            require_match(
                r"^#define\s+END_SEND_OFFSET\s+(\d+)\s*$",
                sources["Python/assemble.c"],
                "END_SEND offset",
            ).group(1)
        )
        lines.append(f"pub(crate) const END_SEND_OFFSET: u32 = {end_send_offset};")
        small_ints = require_definitions(
            parse_numeric_defines(
                sources["Include/internal/pycore_runtime_structs.h"], "_PY_NSMALL"
            ),
            {"_PY_NSMALLNEGINTS", "_PY_NSMALLPOSINTS"},
            "small integer singleton bounds",
        )
        lines.append(
            f"pub(crate) const SMALL_INT_MIN: i64 = -{small_ints['_PY_NSMALLNEGINTS']};"
        )
        lines.append(
            f"pub(crate) const SMALL_INT_MAX: i64 = {small_ints['_PY_NSMALLPOSINTS'] - 1};"
        )
        lines.append("")
    lines.append("#[cfg(test)]")
    lines.append("pub(crate) static PREINTERNED_STRINGS: &[&str] = &[")
    lines.extend(f"    {rust_string_literal(value)}," for value in preinterned_strings)
    lines.extend(["];", ""])
    lines.extend(
        [
            "// Builtin compile() initializes these AST identifiers before compiling source.",
            "#[cfg(test)]",
            "pub(crate) static COMPILER_INTERNED_STRINGS: &[&str] = &[",
        ]
    )
    lines.extend(
        f"    {rust_string_literal(value)}," for value in compiler_interned_strings
    )
    lines.extend(["];", ""])
    if TARGET_MINOR == "3.14":
        bootstrap_strings = read_bootstrap_strings(sources)
        lines.extend(
            [
                "// Source-derived identifiers and live owners from neutral Linux bootstrap.",
                "#[cfg(test)]",
                "pub(crate) static BOOTSTRAP_INTERNED_STRINGS: &[&str] = &[",
            ]
        )
        lines.extend(
            f"    {rust_string_literal(value)}," for value in bootstrap_strings
        )
        linux_preinterned_strings = sorted(
            set(preinterned_strings)
            | set(bootstrap_strings)
            | set(read_startup_strings())
        )
        lines.extend(
            [
                "];",
                "",
                "// Use the canonical isolated Linux profile regardless of the Rust host architecture.",
                '#[cfg(all(test, target_os = "linux"))]',
                "#[rustfmt::skip]",
                "pub(super) static LINUX_PREINTERNED_STRINGS: &[&str] = &[",
            ]
        )
        lines.extend(render_compact_rust_strings(linux_preinterned_strings))
        lines.extend(["];", "", '#[cfg(target_os = "linux")]'])
        lines.extend(render_preinterned_lookup(linux_preinterned_strings, ()))
        lines.extend(["", '#[cfg(not(target_os = "linux"))]'])
        lines.extend(
            render_preinterned_lookup(
                preinterned_strings,
                STARTUP_INTERNED_STRINGS + UNIX_STARTUP_INTERNED_STRINGS,
                tuple(compiler_interned_strings),
            )
        )
    else:
        lines.extend(
            [
                "// Captured before the isolated minimal C reference parses any source.",
                "// Installation paths are supplied only through an explicit InitialInternState.",
                "pub(crate) static STARTUP_INTERNED_STRINGS: &[&str] = &[",
            ]
        )
        lines.extend(
            f"    {rust_string_literal(value)}," for value in read_startup_strings()
        )
        lines.extend(["];", ""])
        lines.extend(
            [
                "pub(crate) fn is_preinterned_string(value: &str) -> bool {",
                "    static STARTUP: std::sync::LazyLock<rustc_hash::FxHashSet<&'static str>> =",
                "        std::sync::LazyLock::new(|| STARTUP_INTERNED_STRINGS.iter().copied().collect());",
                "    is_preinterned_static_string(value)",
                '        || (cfg!(target_os = "linux") && STARTUP.contains(value))',
                "}",
                "",
            ]
        )
        lookup = render_preinterned_lookup(
            preinterned_strings,
            (),
            tuple(compiler_interned_strings),
            compiler_strings_on_linux=False,
        )
        lookup[0] = "fn is_preinterned_static_string(value: &str) -> bool {"
        lines.extend(lookup)
    jumps = {name for name in opcode_names if "HAS_JUMP_FLAG" in opcode_flags[name]}
    expression = opcode_match_expression(opcodes, jumps)
    if TARGET_MINOR == "3.14":
        expression = expression.replace("opcode", "self", 1)
        lines.extend(
            [
                "",
                "impl Opcode {",
                "    pub(crate) const fn has_jump(self) -> bool {",
                f"        {expression}",
                "    }",
                "}",
                "",
            ]
        )
    else:
        lines.extend(
            [
                "pub(crate) const fn has_jump(opcode: Opcode) -> bool {",
                f"    {expression}",
                "}",
                "",
            ]
        )
    for name, names in predicates.items():
        if name == "is_unconditional_jump" and TARGET_MINOR != "3.14":
            continue
        lines.extend(
            [
                f"pub(crate) const fn {name}(opcode: Opcode) -> bool {{",
                f"    {opcode_match_expression(opcodes, names)}",
                "}",
                "",
            ]
        )

    lines.extend(["#[allow(dead_code)]", "pub(crate) mod operands {"])
    render_operand_type(lines, "UnaryIntrinsic", unary_intrinsics, "INTRINSIC_")
    render_operand_type(lines, "BinaryIntrinsic", binary_intrinsics, "INTRINSIC_")
    render_operand_type(
        lines, "FunctionAttribute", function_attributes, "MAKE_FUNCTION_"
    )
    render_operand_type(lines, "CommonConstant", common_constants, "CONSTANT_")
    render_operand_type(lines, "BinaryOperation", binary_operations, "NB_")
    lines.extend(
        [
            "    impl BinaryOperation {",
            "        pub(crate) const fn inplace(self) -> Self {",
            "            match self {",
        ]
    )
    for name, _ in binary_operations:
        operation = name.removeprefix("NB_")
        if operation.startswith("INPLACE_") or operation == "SUBSCR":
            continue
        inplace = f"NB_INPLACE_{operation}"
        if inplace not in dict(binary_operations):
            raise ValueError(f"binary operation {name} has no {inplace} variant")
        lines.append(f"                Self::{operation} => Self::INPLACE_{operation},")
    lines.extend(
        [
            "                Self::SUBSCR => Self::SUBSCR,",
            "                _ => self,",
            "            }",
            "        }",
            "    }",
            "",
        ]
    )
    render_operand_type(lines, "ComparisonOperation", comparison_operations, "")
    lines.extend(
        [
            "    impl ComparisonOperation {",
            "        pub(crate) const fn boolean_argument(self) -> u32 {",
            f"            self.0 | {comparison_boolean_mask}",
            "        }",
            "",
            "        pub(crate) const fn force_boolean(argument: u32) -> u32 {",
            f"            argument | {comparison_boolean_mask}",
            "        }",
            "    }",
            "",
        ]
    )
    render_operand_type(lines, "ResumeLocation", resume_locations, "RESUME_")
    lines.extend(
        [
            "    impl ResumeLocation {",
            "        pub(crate) const fn at_depth(self, depth_one: bool) -> u32 {",
            "            let location = self.0 & "
            f"{resume_values['RESUME_OPARG_LOCATION_MASK']};",
            "            if depth_one {",
            f"                location | {resume_values['RESUME_OPARG_DEPTH1_MASK']}",
            "            } else {",
            "                location",
            "            }",
            "        }",
            "    }",
            "",
        ]
    )
    if TARGET_MINOR == "3.15":
        import_shift, import_modes = parse_import_modes(codegen)
        render_operand_type(lines, "ImportMode", import_modes, "")
        lines.extend(
            [
                "    impl ImportMode {",
                "        /// Encode a name-table index with the selected import behavior.",
                "        pub(crate) const fn encode_name(self, index: u32) -> u32 {",
                f"            (index << {import_shift}) | self.0",
                "        }",
                "    }",
                "",
            ]
        )
        iterator_modes = parse_numeric_defines(opcode_utils, "GET_ITER_")
        require_definitions(
            iterator_modes, {"GET_ITER_YIELD_FROM"}, "iterator mode table"
        )
        render_operand_type(lines, "IteratorMode", iterator_modes, "GET_ITER_")
    render_operand_type(lines, "Conversion", conversions, "FVC_")
    render_operand_type(lines, "SpecialMethod", special_methods, "SPECIAL_")
    lines.extend(["}", "", "#[allow(dead_code)]", "pub(crate) mod code_flags {"])
    for name, value in code_flags:
        lines.append(f"    pub(crate) const {name}: u32 = {rust_hex(value, 8)};")
    lines.extend(["}", ""])
    if TARGET_MINOR == "3.15":
        # Both targets currently share the local layout, but retain the selected
        # release's authoritative definitions for verification and future changes.
        lines.append("#[allow(dead_code)]")
    lines.append("pub(crate) mod local_kinds {")
    for name, value in local_kinds:
        lines.append(f"    pub(crate) const {name}: u8 = {rust_hex(value, 2)};")
    lines.extend(["}", ""])

    lines.extend(
        [
            "pub(crate) fn stack_counts(opcode: Opcode, argument: u32) -> (usize, usize) {",
            "    let argument = i64::from(argument);",
            "    let (popped, pushed) = match opcode {",
        ]
    )
    for name, _ in opcodes:
        popped_expression = rust_stack_expression(popped[name])
        pushed_expression = rust_stack_expression(pushed[name])
        lines.append(
            f"        opcodes::{name} => ({popped_expression}, {pushed_expression}),"
        )
    if TARGET_MINOR == "3.15":
        popped_expression = rust_stack_expression(popped["GET_ITER"])
        pushed_expression = rust_stack_expression(pushed["GET_ITER"])
        lines.append(
            f"        opcodes::GET_YIELD_FROM_ITER => ({popped_expression}, {pushed_expression}),"
        )
    lines.extend(
        [
            '        _ => unreachable!("missing generated stack metadata for opcode {}", opcode.code()),',
            "    };",
            "    (",
            '        usize::try_from(popped).expect("negative generated stack-popped count"),',
            '        usize::try_from(pushed).expect("negative generated stack-pushed count"),',
            "    )",
            "}",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def render_marshal(sources: dict[str, str]) -> str:
    marshal_header = sources[MARSHAL_INPUTS[0]]
    marshal_source = sources["Python/marshal.c"]
    version = int(
        require_match(
            r"^#define\s+Py_MARSHAL_VERSION\s+(\d+)$",
            marshal_header,
            "marshal version",
        ).group(1)
    )
    if version != TARGETS[TARGET_MINOR][3]:
        raise ValueError(f"unexpected marshal version {version}")

    required_tags = {
        "TYPE_NONE",
        "TYPE_FALSE",
        "TYPE_TRUE",
        "TYPE_ELLIPSIS",
        "TYPE_BINARY_FLOAT",
        "TYPE_BINARY_COMPLEX",
        "TYPE_LONG",
        "TYPE_STRING",
        "TYPE_TUPLE",
        "TYPE_CODE",
        "TYPE_UNICODE",
        "TYPE_FROZENSET",
        "TYPE_SLICE",
        "TYPE_INTERNED",
        "TYPE_ASCII",
        "TYPE_ASCII_INTERNED",
        "TYPE_SHORT_ASCII",
        "TYPE_SHORT_ASCII_INTERNED",
        "TYPE_INT",
        "TYPE_SMALL_TUPLE",
        "TYPE_REF",
    }
    if version >= 6:
        required_tags.add("TYPE_FROZENDICT")
    if version < 5:
        required_tags.remove("TYPE_SLICE")
    all_tags = parse_character_defines(marshal_source, "TYPE_")
    tags = [definition for definition in all_tags if definition[0] in required_tags]
    require_definitions(tags, required_tags, "marshal type-tag table")
    flag_ref = require_definitions(
        parse_character_defines(marshal_source, "FLAG_"),
        {"FLAG_REF"},
        "marshal flag table",
    )["FLAG_REF"]

    lines = [
        "// @generated by scripts/generate_cpython_target.py; do not edit.",
        f"// CPython marshal format {version} from {TARGET_TAG} ({TARGET_COMMIT}).",
    ]
    if version == 4:
        lines[1] = (
            "// CPython marshal format 4 shared by the pinned 3.12 and 3.13 targets."
        )
        for minor, expected in V4_INPUT_DIGESTS.items():
            tag, commit, _, _ = TARGETS[minor]
            lines.append(f"// {tag} ({commit}):")
            for relative, digest in expected.items():
                if minor == TARGET_MINOR:
                    actual = hashlib.sha256(sources[relative].encode()).hexdigest()
                    if actual != digest:
                        raise ValueError(
                            f"unexpected marshal-v4 input {relative} for {minor}"
                        )
                lines.append(f"// {relative}: sha256:{digest}")
    else:
        for relative in MARSHAL_INPUTS:
            digest = hashlib.sha256(sources[relative].encode()).hexdigest()
            lines.append(f"// {relative}: sha256:{digest}")
    lines.extend(
        [
            "",
            "#![allow(dead_code)]",
            "",
            f"pub(super) const MARSHAL_VERSION: u8 = {version};",
            f"pub(super) const FLAG_REF: u8 = {rust_byte(flag_ref)};",
        ]
    )
    for name, value in tags:
        lines.append(f"pub(super) const {name}: u8 = {rust_byte(value)};")
    lines.append("")
    return "\n".join(lines)


def check_numeric_authority() -> None:
    paths = [CRATE_ROOT / "src" / "compiler.rs"]
    paths.extend(sorted((CRATE_ROOT / "src" / "compiler").rglob("*.rs")))
    paths.extend(sorted((CRATE_ROOT / "src" / "assembler").rglob("*.rs")))
    operand_opcodes = (
        "BINARY_OP",
        "CALL_INTRINSIC_1",
        "CALL_INTRINSIC_2",
        "COMPARE_OP",
        "CONVERT_VALUE",
        "LOAD_COMMON_CONSTANT",
        "LOAD_SPECIAL",
        "RESUME",
        "SET_FUNCTION_ATTRIBUTE",
    )
    raw_operand = re.compile(
        rf"\b(?:{'|'.join(operand_opcodes)})\s*,\s*(?:0x[0-9A-Fa-f]+|\d+)"
    )
    opcode_names = parse_opcodes_from_generated_names()
    for path in paths:
        relative = path.relative_to(CRATE_ROOT)
        source = path.read_text()
        if re.search(r"Opcode::new\s*\(", source):
            raise ValueError(f"{relative} constructs Opcode outside the target module")
        for match in raw_operand.finditer(source):
            # Inspect the suffix after matching the full numeric token. Putting
            # this exclusion in the regex could backtrack to a digit prefix.
            if re.match(r"\s*=>", source[match.end() :]):
                continue
            raise ValueError(
                f"{relative} duplicates a numeric target operand near `{match.group(0)}`"
            )
        for name in opcode_names:
            pattern = rf"^\s*const\s+{re.escape(name)}\s*:\s*u8\s*=\s*\d+"
            if re.search(pattern, source, re.MULTILINE):
                raise ValueError(f"{relative} duplicates numeric opcode {name}")

    for path in sorted((CRATE_ROOT / "src" / "marshal").rglob("*.rs")):
        if path.name in {"v4.rs", "v5.rs", "v6.rs"}:
            continue
        relative = path.relative_to(CRATE_ROOT)
        if re.search(
            r"^\s*const\s+(?:FLAG_REF|MARSHAL_VERSION|TYPE_[A-Z0-9_]+)\s*:",
            path.read_text(),
            re.MULTILINE,
        ):
            raise ValueError(
                f"{relative} duplicates generated marshal protocol constants"
            )


def parse_opcodes_from_generated_names(
    output: Path = CRATE_ROOT / "src" / "target" / "cpython_3_14_5.rs",
) -> set[str]:
    if not output.exists():
        return set()
    return set(
        re.findall(
            r"^\s*pub\(crate\) const ([A-Z][A-Z0-9_]*): Opcode",
            output.read_text(),
            re.MULTILINE,
        )
    )


def main() -> int:
    options = parse_args()
    select_target_version(options.target_version)
    try:
        verify_checkout(options.cpython)
        sources = read_inputs(options.cpython)
        generated = format_rust(render(sources))
        generated_marshal = format_rust(render_marshal(sources))
        outputs = [(OUTPUT, generated), (MARSHAL_OUTPUT, generated_marshal)]
        if TARGET_MINOR in {"3.12", "3.13"}:
            from generate_legacy_target import render_legacy_opcodes
            from legacy_opcode_metadata import parse_312_metadata, parse_313_metadata

            metadata = (
                parse_312_metadata if TARGET_MINOR == "3.12" else parse_313_metadata
            )(sources)
            outputs.append(
                (
                    CRATE_ROOT / "src" / "target" / "legacy_opcodes.rs",
                    format_rust(render_legacy_opcodes(metadata)),
                )
            )
        if options.check:
            stale = False
            for output, expected in outputs:
                current = output.read_text() if output.exists() else ""
                if current != expected:
                    stale = True
                    sys.stderr.writelines(
                        difflib.unified_diff(
                            current.splitlines(keepends=True),
                            expected.splitlines(keepends=True),
                            fromfile=str(output),
                            tofile=f"{output} (generated)",
                        )
                    )
            if stale:
                return 1
            check_numeric_authority()
            return 0
        for output, generated in outputs:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(generated)
        return 0
    except (OSError, subprocess.CalledProcessError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
