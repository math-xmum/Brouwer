# Development, Builds, and Validation

Run the following commands from the repository root unless stated otherwise.

## Environment requirements

The repository configuration pins:

- Lean `4.33.0`: `lean-toolchain` contains `leanprover/lean4:v4.33.0`.
- mathlib `v4.33.0`: declared in `lakefile.lean`.
- Exact mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`: recorded in `lake-manifest.json`.

Use `elan` to install and select Lean. First check that the commands are available:

```sh
elan --version
lake --version
```

When you run `lake` inside the repository, `elan` selects the version specified by `lean-toolchain`. Obtaining the Lean toolchain or Lake dependencies for the first time requires network access.

## Full build

```sh
lake build
```

This is the standard validation command documented by the root `README.md`, the manuscript instructions, and the GitHub Actions configuration. The default target covers the `GameTheory.lean` umbrella module and the `Gametheory` submodules.

Builds generate or update caches and intermediate artifacts under `.lake/`. Distinguish these changes from handwritten source, and inspect the workspace state before cleaning `.lake/`.

## Quick single-file checks

While editing a Lean file, check it directly:

```sh
lake env lean Gametheory/Nash.lean
```

Replace the path with the file being edited. To check the umbrella entry point, use:

```sh
lake env lean GameTheory.lean
```

Lean loads the file's compiled dependencies, making this useful for quick feedback. Run `lake build` before committing to rebuild dependencies and cover all modules included by the library glob, including those outside the file's dependency chain.

## What testing means in this repository

The guide's inspection found no:

- `test/` or `tests/` directory;
- separate test executable target in `lakefile.lean`;
- conventional unit-test framework or coverage configuration.

Validation therefore consists of:

1. Lean elaboration of an individual file or the umbrella module: `lake env lean ...`.
2. A full library build: `lake build`, which also checks the client examples in `Gametheory/Examples/ScarfPrimitive.lean`.
3. An axiom audit: building `GameTheory.lean` imports `Gametheory/AxiomAudit.lean`, which runs `#print axioms` on the main endpoints.
4. Additional CI checks: `.github/workflows/lean.yml` uses `leanprover/lean-action@v1` with `build: true`, `nanoda: true`, and `nanoda-allow-sorry: false`.

The repository does not document an exact local equivalent of the CI `nanoda` step, so none is supplied here. Remote CI can only run the workflow committed to the relevant branch; check that branch's contents.

For a lightweight static check, search for unfinished proof markers:

```sh
rg -n '\b(sorry|admit|axiom)\b' --glob '*.lean' .
```

This is supplementary and does not replace a Lean build or `nanoda`. The search found no matches in the project `.lean` sources when the guide was assembled.

## Common development commands

```sh
# Inspect existing changes before deciding which files belong to your work.
git status --short

# Read the project's declared Lean toolchain.
sed -n '1p' lean-toolchain

# Inspect direct imports in each module.
rg -n '^import ' --glob '*.lean' .

# Find top-level declarations.
rg -n '^(theorem|lemma|def|structure|abbrev) ' Gametheory

# Build the entire library.
lake build
```

Preserve existing workspace changes. In particular, do not use Git commands that discard modifications to troubleshoot caches, or delete `.lake/`, `paper/`, `output/`, or `tmp/` without understanding their ownership and contents.

## Suggested checks after editing

1. Use `git status --short` to identify changes already present at the start.
2. Edit the target module and run `lake env lean path/to/module.lean`.
3. If definitions or imports changed, check all downstream modules; `lake build` is the most reliable approach.
4. Check for new `sorry`/`admit` markers and inspect whether the `AxiomAudit` output matches expectations.
5. Review `git status --short` and the diff again to avoid committing generated files as source.

The repository provides no formatter, lint command, or explicit style guide. Unless the maintainer specifies otherwise, follow the naming, namespaces, and proof layout of adjacent Lean code.

## Dependencies and reproducibility

To reproduce the pinned dependencies, retain `lake-manifest.json` and build directly. The root `README.md` explicitly advises against running `lake update` when preparing a frozen submission artifact, because it may change locked dependency revisions.

A Lean or mathlib upgrade is a separate maintenance task. At minimum, check these together:

- `lean-toolchain`;
- the mathlib tag in `lakefile.lean`;
- the newly resolved `lake-manifest.json`;
- a full build of all Lean modules and the axiom audit output.

The repository does not document a dependency-upgrade policy; consult the maintainer before upgrading.

## Manuscript draft (optional, outside the Lean build)

The local workspace inspected for this guide contained `paper/cpp2027/`, whose README gives this command:

```sh
cd paper/cpp2027
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
```

This requires a separate LaTeX/`latexmk` installation. The directory was untracked when the guide was assembled, and `lake build` does not build it. Skip this section if it is absent from your clone.

## Recorded validation scope

When this guide was assembled, the following checks were recorded:

- `elan` and `lake` were available; `lake --version` reported Lean `4.33.0`.
- `GameTheory.lean` imported seven proof modules and `AxiomAudit.lean`.
- Direct imports in `Gametheory/*.lean` matched the diagram in [structure.md](structure.md).
- No `sorry`, `admit`, or `axiom` keywords were found in the project `.lean` files.
- `lake env lean GameTheory.lean` succeeded.
- `lake build` succeeded with `Build completed successfully (8715 jobs)`; the additional job explicitly built the umbrella module `GameTheory.lean`. `AxiomAudit` reported `propext`, `Classical.choice`, and `Quot.sound` for each listed endpoint.

These results describe the workspace on 2026-08-17 and validate only that state. Source or dependency changes require fresh validation.
