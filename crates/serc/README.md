# Serc

A Rust library for compiling Python source to CPython bytecode without embedding
a Python runtime. See the [project README](../../README.md) for installation and
CLI usage, [architecture](ARCHITECTURE.md) for internals, and
[development guide](../../docs/development.md) for local checks.

## Library source API

`compile_bytes` accepts source bytes without filesystem I/O. It validates
encoding cookies and UTF-8 BOMs, rejects null bytes, and normalizes CRLF and CR
newlines. Supported encodings are UTF-8, ASCII, Latin-1, Latin-9, EUC-JP,
KOI8-R, and Windows-1251. `compile` accepts decoded UTF-8 text. Both default to
Python 3.14 and reject filenames containing a null character before processing
the source.

When the source timestamp is known, `compile_bytes_to_pyc` also writes a
timestamp-invalidated header with the original source byte length:

```rust
let source = b"# coding: utf-8\r\nanswer = 42\r\n";
let pyc = serc::compile_bytes_to_pyc(source, "module.py", 1_700_000_000).unwrap();
```

Select another target with `CompileOptions`:

```rust
use serc::{CompileOptions, PythonVersion, compile_bytes_with_options};

let options = CompileOptions {
    python_version: PythonVersion::Py315,
    ..CompileOptions::default()
};
let module = compile_bytes_with_options(b"answer = 42\n", "module.py", &options).unwrap();
let pyc = module.to_timestamp_pyc(1_700_000_000, 12);
```

`PythonVersion` also provides `Py312`, `Py313`, and `Py314`. The returned
`CompiledModule` retains the selected target for marshal and `.pyc` output.

Set `CompileOptions::optimization_level` to `OptimizationLevel::One` for
Python's `-O` behavior (remove assertions and set `__debug__` to false), or
`OptimizationLevel::Two` for `-OO` behavior (also remove docstrings):

```rust
use serc::{CompileOptions, OptimizationLevel, compile_with_options};

let options = CompileOptions {
    optimization_level: OptimizationLevel::Two,
    ..CompileOptions::default()
};
let module = compile_with_options("assert condition\n", "module.py", &options).unwrap();
```

The default, `OptimizationLevel::Zero`, retains assertions and docstrings and
sets `__debug__` to true. Optimization is available for all Python targets.

`compile_with_options` accepts UTF-8 text;
`CompileOptions::initial_intern_state` supplies an oracle process's existing
interned strings. Partial intern states reject unresolved membership when it can
affect marshal sharing. `compile_bytes_with_path_and_options` accepts a
filesystem path and preserves filename values that Rust strings cannot
represent, including non-UTF-8 filenames on Unix. It also rejects paths
containing a null character before decoding the source.

Use `compile_with_options_and_integer_limits` to select the integer-string
conversion limit in effect while parsing decimal literals. Its `parse_limit`
argument accepts zero for unlimited conversion, or a limit from 640 through
`i32::MAX`. The separate `mapping_key_limit` argument optionally establishes the
limit when formatting duplicate mapping keys. The existing entrypoints retain
the default 4,300-digit parsing limit and conservative handling of diagnostics
that depend on an unestablished parsing limit. Corresponding bytes and path
entrypoints accept the same explicit limits.

`CompileOptions::native_build_profile` selects instruction ordering for specific
native builds before constant folding. See the
[native arithmetic profiles](../../docs/cpython-build-profiles.md) for artifact
identities and math-library qualification requirements.

Filesystem callers should snapshot metadata before reading the source, then pass
that timestamp and raw byte length to `to_timestamp_pyc`. This prevents a
concurrent edit from receiving a cache header that incorrectly marks the new
source as fresh.

## Embedding footprint

Call only the APIs your application needs so the linker can discard unused
decoding and serialization code. Use `compile` when your application already
has decoded text, and `CompiledModule::bytecode` when it needs only the module's
raw instruction stream. The text API does not model source-codec effects on
CPython's interned-string state, and the instruction stream alone is not a code
object or an importable `.pyc` file. Use the byte-source and marshal or `.pyc`
APIs when those semantics are required.

The final application controls its Cargo release profile. Setting
`strip = "symbols"` in that profile can reduce the executable's disk size
without changing generated machine code, at the cost of symbol names used for
debugging and profiling.

## CPython corpus comparison

The [compatibility guide](../../docs/compatibility.md) documents the frozen
corpus gates, direct comparator usage, results, and oracle startup-state
limitations.

## Updating the CPython target

Generated opcode, stack, code-object, marshal, and startup metadata use these
exact releases:

| Target | CPython tag  | Commit                                     | Magic number |
| ------ | ------------ | ------------------------------------------ | ------------ |
| `3.12` | `v3.12.14`   | `2abcf904b8dac8c999d2b3aac76681abb333798a` | `cb0d0d0a`   |
| `3.13` | `v3.13.15`   | `4061bc4c35f7c26f25264666d4ba083b93d2f6f9` | `f30d0d0a`   |
| `3.14` | `v3.14.5`    | `5607950ef232dad16d75c0cf53101d9649d89115` | `2b0e0d0a`   |
| `3.15` | `v3.15.0rc2` | `435c9e5a798c99653e3ab64ce29baed0e4f3dfee` | `520e0d0a`   |

From the repository root, regenerate a target from its pinned CPython checkout:

```console
python3 crates/serc/scripts/generate_cpython_target.py \
  --cpython /path/to/cpython-3.14.5 --target-version 3.14
```

Use the corresponding checkout and `--target-version` for other targets. Append
`--check` to verify without writing. The generator rejects other commits, reads
committed inputs, and records their hashes. Do not hand-edit generated files in
`src/target` or `src/marshal`.
[Startup supplements](scripts/target_metadata/README.md) require a separately
verified capture.

Adding a target also requires auditing CPython's compiler, assembler,
code-object, and marshal semantics, wiring parser/oracle selection, and passing
the [compatibility gates](../../docs/compatibility.md). Generated tables alone
do not provide language support.

## Benchmarks

Use the [benchmark suite](../serc_benchmark/README.md) for compile/marshal
phases and corpus timing, or the
[Hyperfine harness](../../scripts/benchmarks/README.md) for end-to-end CLI
timing.
