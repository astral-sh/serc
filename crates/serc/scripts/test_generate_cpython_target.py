from __future__ import annotations

import hashlib
import importlib.util
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

SCRIPT = Path(__file__).with_name("generate_cpython_target.py")
SPEC = importlib.util.spec_from_file_location("generate_cpython_target", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
generator = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(generator)


def git(checkout: Path, *arguments: str) -> str:
    return subprocess.run(
        ["git", "-C", str(checkout), *arguments],
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout.rstrip("\n")


class ReadInputsTest(unittest.TestCase):
    def test_parses_only_compiler_initialized_identifiers(self) -> None:
        source = """
        static int init_identifiers(struct ast_state *state)
        {
            state->right = PyUnicode_InternFromString("right");
            state->body = PyUnicode_InternFromString("body");
            state->left = PyUnicode_InternFromString("left");
            state->left = PyUnicode_InternFromString("left");
            return 0;
}
        PyUnicode_InternFromString("unrelated");
        """
        self.assertEqual(
            generator.parse_compiler_interned_strings(source),
            ["body", "left", "right"],
        )
        with self.assertRaisesRegex(ValueError, "incomplete"):
            generator.parse_compiler_interned_strings(
                source.replace('PyUnicode_InternFromString("body")', "NULL")
            )

    def test_parses_preinterned_strings(self) -> None:
        source = """
        #define STRUCT_FOR_ID(NAME) \\
            STRUCT_FOR_ASCII_STR(#NAME) _py_ ## NAME;
        STRUCT_FOR_STR(anon_module, "<module>")
        STRUCT_FOR_STR(empty, "")
        STRUCT_FOR_ID(sort)
        STRUCT_FOR_ID(alpha)
        STRUCT_FOR_ID(sort)
        """
        self.assertEqual(
            generator.parse_preinterned_strings(source),
            ["", "<module>", "alpha", "sort"],
        )
        self.assertEqual(
            generator.parse_preinterned_strings(
                source + "\n        STRUCT_FOR_ID(NAME)\n"
            ),
            ["", "<module>", "NAME", "alpha", "sort"],
        )

    def test_reads_pinned_commit_instead_of_dirty_worktree(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            checkout = Path(directory)
            git(checkout, "init", "--quiet")

            expected = {}
            for relative in generator.TARGET_INPUTS + generator.MARSHAL_INPUTS:
                source = f"committed contents of {relative}\n"
                expected[relative] = source
                path = checkout / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)

            git(checkout, "add", ".")
            git(
                checkout,
                "-c",
                "user.name=Serc test",
                "-c",
                "user.email=serc-test@example.com",
                "commit",
                "--quiet",
                "-m",
                "fixture",
            )
            commit = git(checkout, "rev-parse", "HEAD^{commit}")
            dirty_input = generator.TARGET_INPUTS[0]
            (checkout / dirty_input).write_text("dirty working-tree contents\n")

            with mock.patch.object(generator, "TARGET_COMMIT", commit):
                sources = generator.read_inputs(checkout)

            self.assertEqual(sources, expected)
            self.assertEqual(git(checkout, "rev-parse", "HEAD^{commit}"), commit)
            self.assertEqual(git(checkout, "status", "--short"), f" M {dirty_input}")


class NumericAuthorityTest(unittest.TestCase):
    def test_checks_root_and_nested_compiler_modules(self) -> None:
        cases = (
            ("const LOAD_CONST: u8 = 82;\n", "duplicates numeric opcode LOAD_CONST"),
            ("emit(BINARY_OP, 0);\n", "duplicates a numeric target operand"),
            ("Opcode::new(82);\n", "constructs Opcode outside the target module"),
            (
                "emit(LOAD_COMMON_CONSTANT,13);\n",
                "duplicates a numeric target operand near `LOAD_COMMON_CONSTANT,13`",
            ),
            (
                "emit(LOAD_COMMON_CONSTANT,\n    313);\n",
                "duplicates a numeric target operand",
            ),
            (
                "match slot { 12 => LOAD_COMMON_CONSTANT, 313 => POP_JUMP_IF_FALSE };\n"
                "emit(LOAD_COMMON_CONSTANT,37);\n",
                "duplicates a numeric target operand near `LOAD_COMMON_CONSTANT,37`",
            ),
            (
                "match slot { 12=>LOAD_COMMON_CONSTANT,0x13f=>POP_JUMP_IF_FALSE };\n"
                "emit(LOAD_COMMON_CONSTANT,0x1f);\n",
                "duplicates a numeric target operand near `LOAD_COMMON_CONSTANT,0x1f`",
            ),
        )
        match_arms = (
            "match slot { 12 => LOAD_COMMON_CONSTANT,\n    13 => POP_JUMP_IF_FALSE };\n",
            "match slot { 12=>LOAD_COMMON_CONSTANT,313=>POP_JUMP_IF_FALSE };\n",
            "match slot { 12=>LOAD_COMMON_CONSTANT,0x13f=>POP_JUMP_IF_FALSE };\n",
        )
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            paths = [root / "src/compiler.rs", root / "src/compiler/expression.rs"]
            for path in paths:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("")
            with (
                mock.patch.object(generator, "CRATE_ROOT", root),
                mock.patch.object(
                    generator,
                    "parse_opcodes_from_generated_names",
                    return_value={"LOAD_CONST"},
                ),
            ):
                generator.check_numeric_authority()
                for path in paths:
                    for source in match_arms:
                        with self.subTest(path=path.relative_to(root), source=source):
                            path.write_text(source)
                            try:
                                generator.check_numeric_authority()
                            finally:
                                path.write_text("")
                    for source, message in cases:
                        with self.subTest(path=path.relative_to(root), source=source):
                            path.write_text(source)
                            try:
                                with self.assertRaisesRegex(
                                    ValueError, message
                                ) as raised:
                                    generator.check_numeric_authority()
                                self.assertIn(
                                    str(path.relative_to(root)), str(raised.exception)
                                )
                            finally:
                                path.write_text("")


class RenderPreinternedLookupTest(unittest.TestCase):
    def test_escapes_rust_string_literals(self) -> None:
        self.assertEqual(
            generator.rust_string_literal('quote" slash\\ \n\r\t\0 ☃\x01\x7f'),
            '"quote\\" slash\\\\ \\n\\r\\t\\0 ☃\\x01\\x7f"',
        )

    def test_compact_rust_strings_wrap_only_between_literals(self) -> None:
        long = "x" * 85
        self.assertEqual(
            generator.render_compact_rust_strings([long, 'quote"', "two words"]),
            [f'    "{long}",', '    "quote\\"", "two words",'],
        )

    def test_renders_combined_strings_in_prefix_buckets(self) -> None:
        static = ["", "alpha", "beta"]
        bootstrap = ["alpine", "beta", "méthode"]
        rendered = generator.render_preinterned_lookup(
            sorted(set(static) | set(bootstrap)),
            ("albatross",),
        )
        self.assertIn('            &["alpha", "alpine"]', rendered)
        self.assertIn('        0x6265 => &["beta"],', rendered)
        self.assertIn('        0x6dc3 => &["méthode"],', rendered)
        self.assertIn("    candidates.binary_search(&value).is_ok()", rendered)

    def test_gates_unix_startup_candidates(self) -> None:
        rendered = generator.render_preinterned_lookup(
            ["package"], ("patterns", "pause")
        )
        self.assertIn(
            '            if value == "patterns" || (cfg!(unix) && value == "pause") {',
            rendered,
        )

    def test_preserves_compiler_aliases_only_in_non_linux_fallback(self) -> None:
        arguments = (["static"], ("retained",), ("", "left", "retained", "static"))
        original = generator.render_preinterned_lookup(*arguments)
        native = generator.render_preinterned_lookup(
            *arguments, compiler_strings_on_linux=False
        )
        self.assertIn("        [] => return true,", original)
        self.assertIn('        0x6c65 => return value == "left",', original)
        self.assertIn('        [] => return cfg!(not(target_os = "linux")),', native)
        self.assertIn(
            '        0x6c65 => return cfg!(not(target_os = "linux")) && value == "left",',
            native,
        )
        for lines in [original, native]:
            self.assertIn('        0x7265 => return value == "retained",', lines)
            self.assertIn('        0x7374 => &["static"],', lines)

    def test_renders_exact_prefix_ranges_and_startup_candidates(self) -> None:
        self.assertEqual(
            generator.render_preinterned_lookup(
                ["", "a", "alpha", "alpine", "beta"],
                ("500", "albatross", "ascii"),
            ),
            [
                "pub(crate) fn is_preinterned_string(value: &str) -> bool {",
                "    let prefix = match value.as_bytes() {",
                "        [] => return true,",
                "        [first] => u16::from(*first) << 8,",
                "        [first, second, ..] => u16::from_be_bytes([*first, *second]),",
                "    };",
                "    let candidates: &[&str] = match prefix {",
                '        0x3530 => return value == "500",',
                '        0x6100 => &["a"],',
                "        0x616c => {",
                '            if value == "albatross" {',
                "                return true;",
                "            }",
                '            &["alpha", "alpine"]',
                "        }",
                '        0x6173 => return value == "ascii",',
                '        0x6265 => &["beta"],',
                "        _ => return false,",
                "    };",
                "    candidates.binary_search(&value).is_ok()",
                "}",
            ],
        )


class TargetSelectionTest(unittest.TestCase):
    def tearDown(self) -> None:
        generator.select_target_version("3.14")

    def test_legacy_targets_have_exact_independent_inputs(self) -> None:
        for minor, version, module, supplement_count in [
            ("3.12", (3, 12, 14), "cpython_3_12_14.rs", 2899),
            ("3.13", (3, 13, 15), "cpython_3_13_15.rs", 2569),
        ]:
            with self.subTest(minor=minor):
                generator.select_target_version(minor)
                self.assertEqual(generator.TARGET_VERSION, version)
                self.assertEqual(generator.OUTPUT.name, module)
                self.assertEqual(generator.MARSHAL_OUTPUT.name, "v4.rs")
                self.assertIn("Python/compile.c", generator.TARGET_INPUTS)
                self.assertNotIn("Python/codegen.c", generator.TARGET_INPUTS)
                self.assertNotIn(
                    "Include/internal/pycore_magic_number.h", generator.TARGET_INPUTS
                )
                self.assertIn(
                    "Lib/importlib/_bootstrap_external.py", generator.TARGET_INPUTS
                )
                self.assertEqual(
                    len(generator.read_startup_strings()), supplement_count
                )
        generator.select_target_version("3.14")
        self.assertEqual(
            generator.TARGET_INPUTS,
            tuple(
                dict.fromkeys(
                    (*generator.MODERN_TARGET_INPUTS, *generator.BOOTSTRAP_INPUTS)
                )
            ),
        )

    def test_minimal_startup_requires_reference_and_repeated_capture(self) -> None:
        generator.select_target_version("3.12")
        relative, _ = generator.startup_input()
        original = json.loads((generator.CRATE_ROOT / relative).read_text())
        reference = (
            generator.CRATE_ROOT.parent.parent / "scripts/cpython-reference.c"
        ).read_bytes()
        generator.validate_minimal_startup_profile(original, reference)
        for mutation in (
            "source",
            "protocol",
            "legacy_protocol",
            "duplicate",
            "failed",
            "different_sets",
            "single_read",
            "changed_output",
            "wrong_count",
            "wrong_thread_count",
            "wrong_build",
        ):
            with self.subTest(mutation=mutation):
                profile = json.loads(json.dumps(original))
                if mutation == "source":
                    profile["reference_source_sha256"] = "0" * 64
                elif mutation == "protocol":
                    profile["reference_protocol"] = "python-wrapper"
                elif mutation == "legacy_protocol":
                    profile["reference_protocol"] = "minimal-v1"
                elif mutation == "duplicate":
                    profile["observations"][1] = profile["observations"][0]
                elif mutation == "failed":
                    profile["observations"][0]["actual_exit"] = 1
                elif mutation == "different_sets":
                    profile["observations"][0]["canonical_sha256"] = "0" * 64
                elif mutation == "single_read":
                    profile["observations"][0]["two_complete_reads_equal"] = False
                elif mutation == "changed_output":
                    profile["observations"][0]["observed_equals_unobserved"] = False
                elif mutation == "wrong_count":
                    profile["observations"][0]["entries"] += 1
                elif mutation == "wrong_thread_count":
                    profile["observations"][0]["thread_count"] = 2
                else:
                    profile["gil_enabled"] = False
                with self.assertRaisesRegex(ValueError, "provenance is incomplete"):
                    generator.validate_minimal_startup_profile(profile, reference)

    def test_shared_legacy_semantic_properties_are_source_checked(self) -> None:
        from generate_legacy_target import render_legacy_opcodes

        for name, flags in [
            ("RETURN_CONST", {"HAS_ARG_FLAG", "HAS_CONST_FLAG"}),
            ("LOAD_CLOSURE", {"HAS_ARG_FLAG", "HAS_FREE_FLAG"}),
            ("KW_NAMES", {"HAS_ARG_FLAG", "HAS_CONST_FLAG"}),
        ]:
            with self.subTest(name=name):
                generated = render_legacy_opcodes({"flags": {name: flags}})
                self.assertIn(f"const {name}: Opcode", generated)
                with self.assertRaisesRegex(ValueError, "semantic properties differ"):
                    render_legacy_opcodes({"flags": {name: set()}})

    def test_selects_exact_release_and_protocol_inputs(self) -> None:
        generator.select_target_version("3.15")
        self.assertEqual(generator.TARGET_TAG, "v3.15.0rc2")
        self.assertEqual(
            generator.TARGET_COMMIT, "435c9e5a798c99653e3ab64ce29baed0e4f3dfee"
        )
        self.assertEqual(generator.TARGET_VERSION, (3, 15, 0))
        self.assertEqual(generator.OUTPUT.name, "cpython_3_15_0rc2.rs")
        self.assertEqual(generator.MARSHAL_OUTPUT.name, "v6.rs")
        self.assertIn("Include/cpython/marshal.h", generator.MARSHAL_INPUTS)
        self.assertIn("Python/assemble.c", generator.TARGET_INPUTS)
        generator.select_target_version("3.14")
        self.assertEqual(generator.TARGET_TAG, "v3.14.5")
        self.assertEqual(generator.TARGET_VERSION, (3, 14, 5))
        self.assertEqual(generator.OUTPUT.name, "cpython_3_14_5.rs")
        self.assertEqual(generator.MARSHAL_OUTPUT.name, "v5.rs")
        self.assertNotIn("Python/assemble.c", generator.TARGET_INPUTS)
        self.assertEqual(generator.MARSHAL_INPUTS[0], "Include/marshal.h")

    def test_startup_fixture_matches_target_and_pinned_digest(self) -> None:
        generator.select_target_version("3.15")
        strings = generator.read_startup_strings()
        self.assertEqual(len(strings), 2652)
        self.assertEqual(strings, tuple(sorted(set(strings))))
        self.assertFalse(any(value.startswith("/") for value in strings))
        with (
            mock.patch.object(generator, "STARTUP_315_SHA256", "0" * 64),
            self.assertRaisesRegex(ValueError, "checksum mismatch"),
        ):
            generator.read_startup_strings()
        with (
            mock.patch.object(generator, "TARGET_COMMIT", "0" * 40),
            self.assertRaisesRegex(ValueError, "does not match"),
        ):
            generator.read_startup_strings()

    def test_314_startup_fixture_has_complete_retained_ownership(self) -> None:
        generator.select_target_version("3.14")
        strings = generator.read_startup_strings()
        self.assertEqual(len(strings), 2537)
        self.assertIn("struct_rusage", strings)
        path = generator.CRATE_ROOT / generator.STARTUP_314_INPUT
        original = json.loads(path.read_text())
        read_bytes = Path.read_bytes
        for mutation in [
            "missing_owner",
            "missing_proof",
            "wrong_count",
            "wrong_build",
        ]:
            with self.subTest(mutation=mutation):
                profile = json.loads(json.dumps(original))
                retention = profile["retention"]
                if mutation == "missing_owner":
                    retention["mortal_owners"].pop("struct_rusage")
                elif mutation == "missing_proof":
                    retention["proved_mortal_entries"] -= 1
                elif mutation == "wrong_count":
                    retention["immortal_dynamic_entries"] += 1
                else:
                    profile["gil_enabled"] = False
                data = json.dumps(profile).encode()
                with (
                    mock.patch.object(
                        Path,
                        "read_bytes",
                        autospec=True,
                        side_effect=lambda candidate, data=data: (
                            data if candidate == path else read_bytes(candidate)
                        ),
                    ),
                    mock.patch.object(
                        generator,
                        "STARTUP_314_SHA256",
                        hashlib.sha256(data).hexdigest(),
                    ),
                    self.assertRaisesRegex(
                        ValueError,
                        "incomplete retained ownership|provenance is incomplete",
                    ),
                ):
                    generator.read_startup_strings()

    def test_opcode_boundary_comes_from_pinned_source(self) -> None:
        source = """
        /* Instruction opcodes for compiled code */
#define CACHE 0
#define RESUME 129
#define SPECIALIZED 130
#define HAVE_ARGUMENT 42
#define MIN_SPECIALIZED_OPCODE 130
        """
        self.assertEqual(
            generator.parse_opcodes(source), [("CACHE", 0), ("RESUME", 129)]
        )
        with self.assertRaisesRegex(ValueError, "first specialized opcode"):
            generator.parse_opcodes(source.replace("MIN_SPECIALIZED_OPCODE", "MISSING"))

    def test_import_modes_come_from_each_codegen_branch(self) -> None:
        source = """
        if (s->v.Import.is_lazy) {
            ADDOP_NAME_CUSTOM(c, loc, IMPORT_NAME, alias->name, names, 3, 1);
        } else {
            if (force_eager) {
                // force eager import in try/except block
                ADDOP_NAME_CUSTOM(c, loc, IMPORT_NAME, alias->name, names, 3, 2);
            } else {
                ADDOP_NAME_CUSTOM(c, loc, IMPORT_NAME, alias->name, names, 3, 0);
            }
        }
        """
        self.assertEqual(
            generator.parse_import_modes(source),
            (3, [("LAZY", 1), ("EAGER", 2), ("DEFAULT", 0)]),
        )
        with self.assertRaisesRegex(ValueError, "disagree"):
            generator.parse_import_modes(source.replace("names, 3, 0", "names, 2, 0"))
        with self.assertRaisesRegex(ValueError, "distinct"):
            generator.parse_import_modes(source.replace("names, 3, 0", "names, 3, 2"))

    def test_metadata_array_length_comes_from_pinned_source(self) -> None:
        source = """
const struct opcode_metadata _PyOpcode_opcode_metadata[271] = {
    [RESUME] = { true, INSTR_FMT_IBC, HAS_ARG_FLAG | HAS_EVAL_BREAK_FLAG },
};
        """
        self.assertEqual(
            generator.parse_opcode_flags(source),
            {"RESUME": {"HAS_ARG_FLAG", "HAS_EVAL_BREAK_FLAG"}},
        )


class BootstrapDerivationTest(unittest.TestCase):
    def test_retained_functions_own_all_nested_code_and_constants(self) -> None:
        from generate_cpython_bootstrap import derive_module

        result = derive_module(
            "def owner():\n"
            "    class Nested:\n"
            "        def method(self):\n"
            "            return ('retained_identifier',)\n"
            "    return Nested\n"
            "raise RuntimeError('must never execute')\n",
            "<frozen example>",
        )
        self.assertIn("owner.<locals>.Nested", result["retained_code_strings"])
        self.assertIn("owner.<locals>.Nested.method", result["retained_code_strings"])
        self.assertIn("retained_identifier", result["retained_code_strings"])
        self.assertIn("<frozen example>", result["retained_code_strings"])
        self.assertEqual(result["retained_code_owners"], ["owner:1"])

    def test_unexecuted_branch_names_are_immortal_but_constants_are_not(self) -> None:
        from generate_cpython_bootstrap import derive_module

        result = derive_module(
            "if _MS_WINDOWS:\n"
            "    def unused(unused_argument):\n"
            "        return 'transient_identifier'\n"
            "else:\n"
            "    def retained(retained_argument):\n"
            "        return 'live_identifier'\n",
            "<frozen example>",
        )
        self.assertIn("unused_argument", result["immortal_identifiers"])
        self.assertNotIn("transient_identifier", result["retained_code_strings"])
        self.assertIn("live_identifier", result["retained_code_strings"])
        self.assertEqual(result["retained_code_owners"], ["retained:5"])

    def test_literal_owners_retain_complete_dictionary_keys_and_values(self) -> None:
        from generate_cpython_bootstrap import derive_module

        result = derive_module(
            "aliases = {'first_alias': 'first_codec', 'second_alias': 'second_codec'}\n"
            "discarded = 'released_identifier'\n"
            "discarded = None\n",
            "encodings/example.py",
        )
        self.assertEqual(
            result["retained_literal_strings"],
            ["first_alias", "first_codec", "second_alias", "second_codec"],
        )
        self.assertNotIn("encodings/example.py", result["retained_code_strings"])

    def test_unverified_lifetimes_fail_closed(self) -> None:
        from generate_cpython_bootstrap import derive_module

        for source in [
            "def owner(): pass\nowner = None",
            "def owner(): pass\ndel owner",
            "def owner(): pass\ndef replace():\n    global owner\n    owner = None",
            "@unknown_decorator\ndef owner(): pass",
            "if unknown_condition:\n    def owner(): pass",
        ]:
            with self.subTest(source=source), self.assertRaises(ValueError):
                derive_module(source, "<frozen example>")


if __name__ == "__main__":
    unittest.main()
