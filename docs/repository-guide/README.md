# Brouwer / Gametheory Repository Guide

This is a quick index for new contributors. The repository uses Lean 4 and mathlib to formalize a proof route from Scarf's combinatorial lemma through Brouwer's fixed-point theorem to the existence of mixed Nash equilibria in finite games.

## Start here

- [scarf-primitive.md](scarf-primitive.md): ScarfPath / Primitive entry points, compilable examples, and migration guidance.
- [structure.md](structure.md): top-level directories, Lean modules, actual imports, and core theorems.
- [development.md](development.md): environment setup, builds, single-file checks, CI checks, and common maintenance commands.
- The root [`README.md`](../../README.md): a project-level account of the mathematical proof route, principal definitions, and theorems.

## At a glance

- Package and Lean library name: `Gametheory` (see `lakefile.lean`).
- Default entry point: `GameTheory.lean` in the repository root.
- Source location: `Gametheory/*.lean`.
- Main final theorem: `ExistsNashEq` in `Gametheory/Nash.lean`.
- Pinned toolchain: Lean `4.33.0` (see `lean-toolchain`).
- Direct dependency: mathlib `v4.33.0`; the manifest records commit `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Validation: the repository has no separate unit-test directory or Lake test target; compiling the entire Lean library is the primary check.

## Quick start

Install `elan` first. From the repository root, run:

```sh
lake build
```

`lean-toolchain` tells `elan` which Lean version to select; `lake-manifest.json` pins the dependencies. The first build must obtain dependencies, so it takes more time and network access than subsequent builds.

After a successful build, you can check an individual module while editing:

```sh
lake env lean Gametheory/Nash.lean
```

Before committing, run the full build again:

```sh
lake build
git status --short
```

`git status --short` is not a test, but it helps identify unexpected generated or modified files. Do not delete unfamiliar changes just to obtain a clean status.

## Suggested reading order

1. `Gametheory/Simplex.lean`: auxiliary constructions for the standard simplex.
2. `Gametheory/Scarf.lean`: the colored room/door combinatorial framework and `Scarf`.
3. `Gametheory/ScarfPath.lean`: the fixed-color graph `G_i` and its path/cycle structure.
4. `Gametheory/Primitive.lean`: primitive/almost-primitive formulations, replacement traces, and coordinate realizations.
5. `Gametheory/Brouwer.lean`: `Brouwer` on a single finite-dimensional standard simplex.
6. `Gametheory/Brouwer_product.lean`: `Brouwer_Product` on a finite product of simplices.
7. `Gametheory/Nash.lean`: finite games, mixed strategies, the Nash map, and `ExistsNashEq`.
8. `Gametheory/AxiomAudit.lean`: `#print axioms` for the main endpoints.

This order follows the mathematical content, rather than the compiler's import order. For example, `Primitive.lean` imports `ScarfPath.lean`, while the direct Nash dependency chain does not import `Primitive.lean`. See [structure.md](structure.md) for the exact relationships.

## Scope of this guide

This guide was assembled from `README.md`, `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, `GameTheory.lean`, the imports and main declarations in `Gametheory/*.lean`, `.github/workflows/lean.yml`, and the locally available `paper/cpp2027/README.md`.

The original guide did not establish the following:

- A dedicated contribution process, code style, or branch policy.
- A separate test suite or coverage configuration.
- A release or packaging process.
- An exact local equivalent of the CI `nanoda` check configured through `leanprover/lean-action@v1`.

Consult the maintainer on these matters rather than inferring policy from this guide.
