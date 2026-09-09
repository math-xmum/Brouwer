# Artifact guide: From Scarf to Nash in Lean

This artifact contains the checked Lean development accompanying the paper
*From Scarf to Nash in Lean: Representation Interfaces for Formalized
Existence Proofs*.  The manuscript displays selected declaration statements;
the files below contain their definitions and checked proofs.

## Environment and one-command check

- Lean: 4.33.0 (`lean-toolchain`)
- Mathlib: 4.33.0, revision
  `db584cd6d46c92f209a44c0f1c829460d327499d` (`lake-manifest.json`)
- Proof-bearing source: eight files, 7,735 physical lines

Install Lean through `elan` if it is not already available.  On a fresh
checkout, the first build also downloads the dependencies recorded in
`lake-manifest.json`; later builds reuse Lake's cache.  Do not run
`lake update`, because evaluation should use the recorded revisions.

From the artifact root, run:

```sh
lake build
```

The default target explicitly builds `GameTheory.lean`, every proof-bearing
module listed below, and `Gametheory/AxiomAudit.lean`.  A successful build
ends with `Build completed successfully`.  When the axiom-audit module is
elaborated, every principal endpoint reports only `propext`,
`Classical.choice`, and `Quot.sound`.

To rerun the trust-boundary report even after an incremental build, use:

```sh
lake env lean Gametheory/AxiomAudit.lean
```

## Paper-to-source map

ScarfPath/Primitive anchors below follow the namespace migration. The
[API guide](docs/repository-guide/scarf-primitive.md) and
[migration table](docs/repository-guide/scarf-primitive-renames.md) also map
older reports to current declarations.

| Paper result or interface | Checked declaration(s) | Source anchor |
|---|---|---|
| Standard simplex operations and weighted-average inequality | `stdSimplex.pure`, `stdSimplex.wsum_magic_ineq` | `Gametheory/Simplex.lean:25`, `Gametheory/Simplex.lean:57` |
| Dominance cardinality | `IndexedLOrder.keylemma_of_dominant`, `IndexedLOrder.card_le_of_isDominant` | `Gametheory/Scarf.lean:128`, `Gametheory/Scarf.lean:159` |
| Exact outside and internal door fibers | `IndexedLOrder.exists_filter_isOutsideDoor_eq_singleton`, `IndexedLOrder.internal_door_two_rooms` | `Gametheory/Scarf.lean:1793`, `Gametheory/Scarf.lean:951` |
| Typed colorful-incidence parity | `IndexedLOrder.odd_card_filter_isColorful` | `Gametheory/Scarf.lean:2149` |
| Scarf certificate | `IndexedLOrder.Scarf` | `Gametheory/Scarf.lean:2164` |
| Fixed-color degree classification | `ScarfPath.degree_characterization` | `Gametheory/ScarfPath.lean:503` |
| Generic degree-two components and the fixed-color instance | `PathComponents.components_have_spanning_paths_or_cycles_of_degree_le_two`, `ScarfPath.component_structure` | `Gametheory/PathComponents.lean:249`, `Gametheory/ScarfPath.lean:596` |
| Primitive encoding and native definition | `Primitive.toPrimitiveSet`, `Primitive.IsPrimitive`, `Primitive.IsAlmostPrimitiveNative` | `Gametheory/Primitive.lean:44`, `Gametheory/Primitive.lean:223`, `Gametheory/Primitive.lean:238` |
| Room/primitive, door/almost-primitive, and full-color dictionary | `Primitive.isPrimitive_toPrimitiveSet_iff_room`, `Primitive.isAlmostPrimitive_iff_native`, `Primitive.almostPrimitive_subset_primitive_iff_doorof`, `Primitive.full_color_primitive_iff_colorful_associated_room` | `Gametheory/Primitive.lean:279`, `Gametheory/Primitive.lean:514`, `Gametheory/Primitive.lean:938`, `Gametheory/Primitive.lean:1104` |
| Primitive supersets and erase-insert replacement | `Primitive.native_almostPrimitive_incident_primitives_boundary_or_internal`, `Primitive.IsPrimitive.erase_replacement` | `Gametheory/Primitive.lean:913`, `Gametheory/Primitive.lean:678` |
| Replacement step to graph walk | `Primitive.SplitStep.edges`, `Primitive.SplitStep.walk` | `Gametheory/Primitive.lean:1367`, `Gametheory/Primitive.lean:1383` |
| Classical terminal trace | `Primitive.Trace`, `Primitive.Trace.nonempty` | `Gametheory/Primitive.lean:1437`, `Gametheory/Primitive.lean:1537` |
| Optional coordinate realization | `Primitive.Coordinate.exists_model`, `Primitive.Coordinate.IsPrimitive.erase_replacement` | `Gametheory/Primitive.lean:2197`, `Gametheory/Primitive.lean:2401` |
| Dominant-room grid estimates | `size_bound_in`, `size_bound_out` | `Gametheory/Brouwer.lean:207`, `Gametheory/Brouwer.lean:320` |
| Standard-simplex Brouwer theorem | `Brouwer` | `Gametheory/Brouwer.lean:734` |
| Flat/dependent index equivalence | `index_split`, `index_combine`, `index_split_combine_inverse`, `index_combine_split_inverse` | `Gametheory/Brouwer_product.lean:105`, `:116`, `:139`, `:204` |
| Adaptive repair | `deficit`, `tPush`, `pushTowardsZ`, `blockSum_pushTowardsZ_pos` | `Gametheory/Brouwer_product.lean:245`, `:249`, `:253`, `:538` |
| Product retraction | `project_embed_id`, `project_continuous`, `embed_continuous` | `Gametheory/Brouwer_product.lean:419`, `:608`, `:634` |
| Brouwer for dependent products | `Brouwer_Product` | `Gametheory/Brouwer_product.lean:662` |
| Finite player/strategy reindexing and fixed-point transport | `reindex`, `reindex_inv`, `reindex_right_inv`, `reindex_left_inv`, `map_simplex_equiv`, `Brouwer.mixedGame` | `Gametheory/Nash.lean:173`, `:176`, `:179`, `:196`, `:228`, `:262` |
| Expected payoff, mixed-equilibrium predicate, payoff linearity, and Nash-map continuity | `FinGame.mixed_g`, `FinGame.mixedNashEquilibrium`, `FinGame.mixed_g_linear`, `FinGame.one_le_sum_g`, `FinGame.nash_map_cont` | `Gametheory/Nash.lean:59`, `:159`, `:61`, `:384`, `:468` |
| Mixed Nash existence | `ExistsNashEq` | `Gametheory/Nash.lean:486` |
| Principal trust-boundary audit | `#print axioms` commands | `Gametheory/AxiomAudit.lean:17` |

## Module roles

The endpoint chain is:

```text
Scarf.lean <- ScarfPath.lean <- Brouwer.lean <- Brouwer_product.lean <- Nash.lean
```

`ScarfPath.lean`, `Primitive.lean`, and `PathComponents.lean` form the
structural branch.  They refine
the finite certificate with graph, primitive-set, replacement, and terminal
trace results. Although `Brouwer` imports `ScarfPath`, the path/trace
endpoints are not premises of its proof or the Nash proof.
`Gametheory/Examples/ScarfPrimitive.lean` supplies client examples checked
by the default build.

`GameTheory.lean` is the umbrella import.  `lakefile.lean` includes that root
module and all `Gametheory` submodules in the default library target, so the
single build command checks both the endpoint chain and the structural branch.

## Rebuilding the manuscript

The paper source is `paper/cpp2027/main.tex`.  From that directory, run:

```sh
latexmk -g -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The resulting review PDF is `paper/cpp2027/main.pdf`.  This PDF and the other
LaTeX intermediates are generated files and are excluded by `.gitignore` from
the source artifact.  Proof terms and implementation bodies are intentionally
kept in the Lean source rather than duplicated in the manuscript.

The Lean source is authoritative.  Manuscript listings reproduce selected
declaration statements; the longer Nash fixed-point-to-equilibrium argument is
proved inline in `ExistsNashEq`, rather than exported as two additional helper
lemmas.

For a source-only release, create the archive from a clean frozen commit with
`git archive`.  The repository's `.gitattributes` excludes historical Lake
caches and local review outputs from such archives; `.gitignore` prevents new
generated Lean and LaTeX files from being added accidentally.

## Scope and trust

The trace theorem returns a classical `Nonempty` witness.  The artifact does
not claim an executable pivot rule, an extracted solver, or a complexity
bound.  The Brouwer endpoints are specialized to standard simplices and the
represented finite dependent products used by the game development.

The proof-bearing files contain no active `sorry` or `admit`, and declare no
custom `axiom`, `unsafe`, or `opaque` command.  The strings `sorry` that remain
in `Gametheory/Nash.lean` occur only inside commented-out experiments.
