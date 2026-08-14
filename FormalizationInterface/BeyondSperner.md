# Beyond Sperner: statement blueprint

This document is the semantic contract for the Lean formalization of the dependency spine leading
to Ivanov's generalized Scarf theorem.  It is meant to be readable both by a human reviewer and by
proof-planning or autoformalization tools such as Rethlas and Archon.

The current milestone combines **statement correctness** with kernel-checked proofs along the main
dependency spine.  A `sorry` marks an open proof obligation; it is not part of the mathematical
interface.

Current proof coverage, including transitive `sorryAx` warnings, is tracked separately in
[`STATUS.md`](STATUS.md).

## Module organization

- `BeyondSperner.Simplicial` and `BeyondSperner.Orders` contain the finite-complex, chain, and
  indexed-order foundations.
- `BeyondSperner.OrientedMatroid` contains signed sets, the weak-circuit core, duality,
  realizability, and the principal and lexicographic extension constructions.
- `BeyondSperner.Coloring`, `BeyondSperner.Scarf`, and `BeyondSperner.FixedPoint` separate coloring
  mechanisms, Scarf theorem families, and fixed-point applications.
- `BeyondSperner.Freudenthal` contains the integer, combinatorial, geometric, and application
  layers of the concrete Freudenthal--Scarf triangulation.
- `BeyondSperner.Euclidean` contains affine geometry and the independent intersection-number
  route, whose production modules use mathematical responsibilities rather than paper numbers.
- `BeyondSperner.Geometry.Triangulation` contains the abstract finite geometric-triangulation
  bridge, purity, non-branching, and applications.
- `FormalizationInterface` remains outside the mathematical tree as the paper-route adapter and
  audit layer; its theorem-numbered filenames are intentional.

## Dependency graph

Module names in the graph are relative to `BeyondSperner`.

```text
OrientedMatroid.SignedSubset
    └── OrientedMatroid.Core
          └── OrientedMatroid.WeakStrongElimination
                └── OrientedMatroid.Basic  ←─ OrientedMatroid.MatroidFromCircuits
          ├── OrientedMatroid.Elimination ── OrientedMatroid.Todd
          ├── OrientedMatroid.Dual ── OrientedMatroid.Farkas
          │                           └── OrientedMatroid.CocircuitElimination
          │                                └── OrientedMatroid.LexicographicLocalization
          └── OrientedMatroid.PrincipalExtension ── OrientedMatroid.LexicographicCircuit
                                      └── OrientedMatroid.LexicographicExtensionConstruction
                                            └── OrientedMatroid.LexicographicExtension

Simplicial.ChainSimplex ── Orders.LinearOrders
      │               │
      └── Coloring.Matroid.Nondegenerate
                    ├── Coloring.Matroid.General
                    └──────────────┬─────────┘
                                   └── Scarf.Generalized

OrientedMatroid.Realizable ── Coloring.Vector ── Scarf.Vector ── FixedPoint.Kakutani
                                      │                 │
                                      └── Theorem 7.2   └── Lemma 7.3 / Scarf.Generalized

Scarf.Classical ── FixedPoint.ScarfBrouwer ── FixedPoint.AffineBrouwer

Euclidean.Chains ── Euclidean.Intersection.Basic
                          └── Euclidean.Intersection.GeneralPosition
                                      └── Euclidean.Intersection.DegenerateSimplex
Euclidean.AffineGeometry ──────────────────────────────┘
                                             └── Euclidean.Intersection.Stokes
                                                   └── Euclidean.Intersection.EnvelopeCoverage
                                                         └── Euclidean.Intersection.AffineColoring
                                                               └── formula (40) adapter
                                                                     ├── Theorem 10.9
                                                                     └── Theorem 10.10

Coloring.Matroid.General ── Coloring.Affine (Theorem 10.8)
                              └── Coloring.AffineEnvelope (Lemma 10.7 conclusion)

Orders.LinearOrders ── Freudenthal.IntegerSimplex
                            └── Freudenthal.CellClassification
                                  └── Freudenthal.Complex ── Freudenthal.DimensionZero
                                        └── Freudenthal.Faces ── Freudenthal.Geometry
                                              └── Freudenthal.Connectivity ── Freudenthal.Boundary
                                                    └── Freudenthal.Isomorphism
                                                          └── Freudenthal.Realization
                                                                └── Freudenthal.GeometricComplex
```

`BeyondSperner` is independent of `Gametheory`.  The latter remains the separate Brouwer/Nash
development.

## Semantic commitments

1. **Signed circuits are primary, and elimination is genuinely weak at the interface.**
   `OrientedMatroid.Data` stores sign reversal, circuit incomparability, and weak circuit
   elimination; it has no strong-elimination field.  On a finite ground type,
   `Data.strongElimination` is derived by contraction induction in
   `OrientedMatroid.WeakStrongElimination`.  An ordinary mathlib matroid is derived from circuit
   supports, so the structure cannot contain two unsynchronised notions of circuit.
2. **Finite underlying-matroid construction.** The theorem constructing the underlying ordinary
   matroid assumes `[Finite α]`.  This is the setting used by the article and avoids silently
   claiming that the chosen finite circuit axioms characterize arbitrary infinite matroids.
3. **Duality is derived rather than postulated.** Signed cocircuits are support-minimal covectors.
   Their strong elimination is proved by a finite Farkas/four-painting argument using only
   support correspondence, sign reversal, and circuit--cocircuit orthogonality.  This constructs
   `Data.dual`, identifies its ordinary underlying matroid with the ordinary dual, and proves
   involutivity; no cocircuit-elimination field is added to `Data`.
4. **The empty simplex is present.** `FiniteSimplicialComplex` is native rather than mathlib's
   `AbstractSimplicialComplex`, because the article includes the empty simplex of dimension `-1`.
5. **Dimension bounds are encoded by cardinality.** Every simplex of `D(A)` has cardinality at
   most `|A|`, i.e. dimension at most `|A|-1`.  A full-cardinality simplex is not built into
   `SimplexFamily`: for arbitrary indexed orders it need not exist.  For example, two identical
   orders on a two-point set have no two-element cell.  Full-cardinality simplices are represented
   separately by `IsTopSimplex` and may form the empty collection.
6. **Chains use `F₂`.** `SimplexFamily.Chain` has coefficients in `ZMod 2`, and its boundary includes
   the empty face of a zero-simplex.
7. **Dominance follows the article's empty-set convention.** `IsDominant σ C` explicitly requires
   `C.Nonempty`.  Thus `∅` is dominant with respect to every nonempty `C`, and nothing is dominant
   with respect to `∅`.
8. **Disjoint unions are structural.** The article's assumption `X ∩ I = ∅` is represented by
   `X ⊕ I`, not by a proposition about two subsets of one ambient type.
9. **The arbitrary tail order is explicit.** A `[LinearOrder I]` chooses the permitted arbitrary
   order among formal indices other than the distinguished one in each extended order.
10. **Paper Lemma 6.1 is repaired explicitly.** Its Lean statement assumes `b ∉ X`.  Without that
   implicit `X ⊆ M - b` condition the printed statement is false, since convex-hull membership
   includes ordinary membership.
11. **Lemma 7.3 assumes a nonempty old ground set.** `[Nonempty X]` excludes the empty-ground-set
    counterexample while matching the generalized Scarf setting.
12. **Lemma 6.3 carries its top-dimensional cardinality context.** The formal statement assumes
    `D.card = Fintype.card I`.  This is the case used in the paper; without it the former arbitrary
    finite-set statement is over-strong.
13. **Realizability is constructed, not asserted.** Signed circuits of a real configuration are
    sign vectors of elementary dependences. The circuit axioms and the compatibility of
    independence, bases, acyclicity, and convex hull with linear algebra are proved before the
    configuration is passed to the coloring theorem. Theorem 7.2 returns a `Module.Basis` and an
    explicit nonnegative coefficient function, not only an oriented-matroid `IsGoodBasis`.
14. **The raw vector Scarf hypotheses are explicit.** The paper's proof of its displayed
    `φ : X ∪ I → ℝ^{n+1}` theorem calls Theorem 7.2 for `M = φ(X ∪ I) + b`.  Accordingly,
    `VectorScarf.RawData` requires old vectors and the standard basis to be different from `b`,
    and `RawData.scarf` explicitly assumes boundedness of the nonnegative solution set of (30).
    The conclusion is stated on the literal finite image `S.image φ`.
15. **Section 9 separates an already fixed sample point.** For the paper's color
    `c(x) = f(x) - x + b`, the equality `c(x) = b` is equivalent to `f(x) = x`.
    Since the raw vector theorem colors old vertices by vectors different from `b`, the Lean
    proof first returns that exact fixed point or proceeds in the no-fixed branch.  Lemma 9.2 is
    correspondingly stated as an exact-fixed-stage alternative or one fixed `C` occurring
    infinitely often; this is the total statement justified for arbitrary selected samples.

## Article-to-Lean statement map

| Article item | Lean declaration | Module |
| --- | --- | --- |
| simplex-family and dimensions | `SimplexFamily` | `BeyondSperner.Simplicial.ChainSimplex` |
| equation (1), pseudo-simplex | `SimplexFamily.IsPseudoSimplex` | `BeyondSperner.Simplicial.ChainSimplex` |
| equation (2), chain-simplex | `SimplexFamily.IsChainSimplex` | `BeyondSperner.Simplicial.ChainSimplex` |
| Theorem 1.2 | `SimplexFamily.IsPseudoSimplex.isChainSimplex` | `BeyondSperner.Simplicial.ChainSimplex` |
| envelope; Theorems 1.5 and 1.6 | `Envelope.family`, `Envelope.pseudo_family`, `Envelope.chain_family` | `BeyondSperner.Simplicial.ChainSimplex` |
| dominance, cells, faces | `IndexedLinearOrders.IsDominant`, `IsCell`, `IsFace` | `BeyondSperner.Orders.LinearOrders` |
| Lemma 2.1 and Corollary 2.2 | `eq_image_min_of_isDominant`, `card_le_of_isDominant` | `BeyondSperner.Orders.LinearOrders` |
| Theorem 2.7 and Corollary 2.9 | `associatedFamily_isPseudoSimplex`, `associatedFamily_isChainSimplex` | `BeyondSperner.Orders.LinearOrders` |
| weak signed-circuit oriented matroid | `OrientedMatroid.Data` | `BeyondSperner.OrientedMatroid.Core` |
| weak-to-strong circuit elimination | `WeakData.strongElimination`, `Data.strongElimination` | `BeyondSperner.OrientedMatroid.WeakStrongElimination` |
| finite Farkas/four-painting alternative | `OrthogonalPair.farkas`, `OrthogonalPair.fourPainting` | `BeyondSperner.OrientedMatroid.Farkas` |
| signed cocircuit elimination and duality | `Data.exists_isCocircuit_strongElimination`, `Data.dual`, `Data.dual_underlying`, `Data.dual_dual` | `BeyondSperner.OrientedMatroid.CocircuitElimination` |
| canonical lexicographic cocircuit signature | `LexFirstSupported`, `lexLift`, `lexLift_sameSignWithin` | `BeyondSperner.OrientedMatroid.LexicographicLocalization` |
| ordinary principal single-element extension and cocircuit-support classification | `PrincipalExtension.matroid`, `matroid_isCocircuit_image_inl_of_disjoint`, `matroid_isCocircuit_insert_new_image_inl_iff` | `BeyondSperner.OrientedMatroid.PrincipalExtension` |
| explicit lexicographic circuit signing and primary cocircuit coverage | `lexCircuit`, `lexSignedCircuits`, `lexCircuit_orthogonal_lexLift`, `exists_lexPrimaryCocircuit_support_of_new_mem` | `BeyondSperner.OrientedMatroid.LexicographicCircuit` |
| conditional exact assembly from secondary signings | `HasSecondaryCocircuitSignings`, `lexOrthogonalPair`, `lexExtensionData`, `lexExtensionData_underlying_eq` | `BeyondSperner.OrientedMatroid.LexicographicExtensionConstruction` |
| strict secondary cocircuit construction | `hasStrictSecondaryCocircuitSignings`, `HasStrictSecondaryCocircuitSignings.toHasSecondary` | `BeyondSperner.OrientedMatroid.LexicographicSecondary` |
| convex hull, acyclicity, good basis | `MemConvexHull`, `IsAcyclic`, `IsGoodBasis` | `BeyondSperner.OrientedMatroid.Basic` |
| Theorem 5.1 and Corollary 5.2 | `strongElimination`, `weakElimination` | `BeyondSperner.OrientedMatroid.Elimination` |
| Todd's theorem | `todd`, `todd_unique` | `BeyondSperner.OrientedMatroid.Todd` |
| nondegenerate framework | `MatroidColoring.Framework`, `Framework.IsNondegenerate` | `BeyondSperner.Coloring.Matroid.Nondegenerate` |
| Lemmas 6.1--6.3 | `not_memConvexHull_of_card_eq_of_not_isBasis`, `existsUnique_goodBasis_replace`, `card_goodReplacements_eq_zero_or_two` | `BeyondSperner.Coloring.Matroid.Nondegenerate` |
| Lemma 6.4 | `boundary_goodBasis_parity` | `BeyondSperner.Coloring.Matroid.Nondegenerate` |
| Theorem 6.5, including parity | `MatroidColoring.theorem6_5` | `BeyondSperner.Coloring.Matroid.Nondegenerate` |
| Lemma 7.3 | `IndexedLinearOrders.dominant_extendCell_iff` | `BeyondSperner.Orders.LinearOrders` |
| Lemma 7.1 | `VectorColoring.Framework.isAcyclic_of_isBounded_nonnegativeSolutions` | `BeyondSperner.Coloring.Vector` |
| realizable vector oriented matroid | `RealizableOrientedMatroid.data` | `BeyondSperner.OrientedMatroid.Realizable` |
| vector/oriented compatibility | `isIndependent_iff_linearIndependent`, `isAcyclic_iff_no_nonnegative_dependence`, `memConvexHull_iff_exists_nonnegative_combination` | `BeyondSperner.OrientedMatroid.Realizable` |
| Theorem 7.2 | `VectorColoring.Framework.theorem7_2` | `BeyondSperner.Coloring.Vector` |
| vector Scarf theorem (packaged framework) | `VectorScarf.vectorScarf` | `BeyondSperner.Scarf.Vector` |
| vector Scarf theorem (direct raw `φ`) | `VectorScarf.RawData.scarf` | `BeyondSperner.Scarf.Vector` |
| Lemma 9.1 | `KakutaniScarf.lemma9_1_coefficient_le_one`, `lemma9_1_isBounded` | `BeyondSperner.FixedPoint.Kakutani` |
| formula (34) and equation (35) | `KakutaniScarf.IsCellSolution`, `IsCellSolution.exists_indexed_coefficients_bounded` | `BeyondSperner.FixedPoint.Kakutani` |
| Lemma 9.2, with exact-fixed branch explicit | `KakutaniScarf.lemma9_2` | `BeyondSperner.FixedPoint.Kakutani` |
| limiting coefficient argument after (36) | `KakutaniScarf.convex_combination_of_limit_equation`, `mem_of_limit_equation` | `BeyondSperner.FixedPoint.Kakutani` |
| Kakutani fixed-point theorem on a finite simplex | `KakutaniScarf.scarf_kakutani_fixedPoint`, `kakutani_fixedPoint` | `BeyondSperner.FixedPoint.Kakutani` |
| Section 10 chain identities | `SimplexFamily.boundary_boundary`, `normalizedMapChainHom_boundary` | `BeyondSperner.Euclidean.Chains` |
| Lemma 10.1 | `EuclideanIntersection.facet_endpoint_parity_pair`, `EuclideanIntersection.lemma10_1` | `BeyondSperner.Euclidean.Intersection.Basic` |
| Lemma 10.2 (`0 < n`) and its zero-dimensional counterexample | `EuclideanIntersection.exists_generalPosition_endpoint`, `EuclideanIntersection.lemma10_2_requires_positive_dimension`, `EuclideanIntersection.lemma10_2` | `BeyondSperner.Euclidean.Intersection.GeneralPosition` |
| Lemma 10.4, including the exact-codimension-one facet parity | `EuclideanIntersection.exists_exactly_two_facets_of_not_isGeneric`, `EuclideanIntersection.facet_point_parity_of_not_isGeneric`, `EuclideanIntersection.lemma10_4` | `BeyondSperner.Euclidean.Intersection.DegenerateSimplex` |
| Theorem 10.5 and Corollary 10.6 | `EuclideanIntersection.chain_stokes_of_pairwise`, `EuclideanIntersection.theorem10_5`, `EuclideanIntersection.corollary10_6` | `BeyondSperner.Euclidean.Intersection.Stokes` |
| Lemma 10.7, forward intersection-number proof | `EuclideanIntersection.lemma10_7_intersection` | `BeyondSperner.Euclidean.Intersection.EnvelopeCoverage` |
| Theorem 10.8, paper's general-position/limit route in envelope form | `EuclideanIntersection.theorem10_8_envelope_intersection` | `BeyondSperner.Euclidean.Intersection.AffineColoring` |
| Theorem 10.8, paper route converted to formula (40) | `AffineColoring.theorem10_8_via_intersection` | `FormalizationInterface.Theorem10_8Intersection` |
| Theorem 10.9, provider-parameterized interior and boundary layers | `AffineColoring.theorem10_9_interior_of_solution_provider`, `theorem10_9_of_interior_provider` | `BeyondSperner.Coloring.VectorHedgehog` |
| Theorem 10.9 through the paper route | `AffineColoring.theorem10_9_via_intersection` | `FormalizationInterface.Theorem10_9Intersection` |
| Lemma 10.3 | `AffineGeometry.lemma10_3_atMost`, `AffineGeometry.lemma10_3` | `BeyondSperner.Euclidean.AffineGeometry` |
| formula (40) and Theorem 10.8, barycentric-coordinate form | `AffineColoring.completedPoints_eq_formula`, `theorem10_8_coordinate` | `BeyondSperner.Coloring.Affine` |
| Theorem 10.8, arbitrary affine basis | `AffineColoring.theorem10_8` | `BeyondSperner.Coloring.Affine` |
| Lemma 10.7 envelope-covering conclusion, derived from Theorem 10.8 without general position | `AffineColoring.lemma10_7_envelope_of_theorem10_8` | `BeyondSperner.Coloring.AffineEnvelope` |
| Theorem 10.9, strict-interior cyclic half-space argument | `AffineColoring.exists_mem_finRotate_not_mem_of_nonempty_ne_univ`, `theorem10_9_interior` | `BeyondSperner.Coloring.VectorHedgehog` |
| Theorem 10.9, finite-closed-union boundary extension | `AffineColoring.isClosed_fullSimplexColorRegion`, `theorem10_9` | `BeyondSperner.Coloring.VectorHedgehog` |
| Theorem 10.9 on the concrete Freudenthal--Scarf triangulation (`0 < N`) | `IntegerSimplex.freudenthal_theorem10_9` | `BeyondSperner.Freudenthal.Applications.VectorHedgehog` |
| arbitrary finite geometric triangulation, induced reference-face family and dimension bound | `GeometricTriangulation.faceComplex`, `family`, `faceComplex_card_le` | `BeyondSperner.Geometry.Triangulation.Core` |
| exact geometric coverage of every induced reference-face complex | `mem_referenceFace_iff_coord`, `exists_faceComplex_simplex_containing`, `realizedFaceComplexSpace_eq_referenceFace` | `BeyondSperner.Geometry.Triangulation.Core` |
| full geometric/abstract face conversion and finite facet extension | `mem_faceComplex_univ_iff`, `abstractFace`, `realize_abstractFace`, `exists_facet_superset` | `BeyondSperner.Geometry.Triangulation.Core` |
| arbitrary geometric face-coordinate and ambient-inclusion obligations | `family_face_coordinate`, `family_subset_full` | `BeyondSperner.Geometry.Triangulation.Core` |
| geometric facet cardinality implies abstract purity | `FacetsHaveCardinality`, `family_full_isPure` | `BeyondSperner.Geometry.Triangulation.Core` |
| automatic purity of a finite geometric triangulation | `interior_lowerDimensionalLocus_eq_empty`, `referenceFace_subset_fullDimensionalSpace`, `exists_full_face_superset`, `facetsHaveCardinality`, `family_full_isPure_of_data` | `BeyondSperner.Geometry.Triangulation.Purity` |
| reference-face intersection, boundary uniqueness, and the pseudo/chain bridge | `referenceFace_inter`, `boundary_index_unique`, `boundaryMembershipCount_eq_one_iff`, `IsNonbranching.isPseudoSimplex`, `IsNonbranching.isChainSimplex` | `BeyondSperner.Geometry.Triangulation.Core` |
| automatic local incidence and non-branching for every finite geometric triangulation | `cofaceCount_eq_one_of_liesInReferenceBoundary`, `cofaceCount_eq_two_of_not_liesInReferenceBoundary`, `isNonbranching` | `BeyondSperner.Geometry.Triangulation.Nonbranching` |
| Theorems 10.9 and 10.10 for an arbitrary finite geometric triangulation | `geometric_theorem10_9`, `geometric_theorem10_10` | `BeyondSperner.Geometry.Triangulation.Applications` |
| arbitrary finite geometric triangulation through the paper route | `geometric_theorem10_9_via_intersection`, `geometric_theorem10_10_via_intersection` | `FormalizationInterface.GeometricApplicationsIntersection` |
| Theorem 10.10, centered-coordinate core | `AffineColoring.theorem10_10_coordinate_core`, `theorem10_10_core` | `BeyondSperner.Coloring.InwardTangent` |
| Theorem 10.10, public-solution coefficient reconstruction | `zero_mem_colorHull_of_affineSolution`, `theorem10_10_core_of_affineSolution`, `theorem10_10_of_core` | `BeyondSperner.Coloring.InwardTangent` |
| Theorem 10.10 through the paper route | `AffineColoring.theorem10_10_via_intersection` | `FormalizationInterface.Theorem10_10Intersection` |
| Theorem 10.10, top-simplex conclusion under explicit triangulation obligations | `AffineColoring.theorem10_10` | `BeyondSperner.Coloring.InwardTangent` |
| positive-scale Freudenthal/associated-complex purity used by Theorem 10.10 | `freudenthalComplex_isPureOfCardinality_of_pos`, `associatedComplex_isPureOfCardinality_of_pos` | `BeyondSperner.Freudenthal.Geometry`, `BeyondSperner.Freudenthal.Boundary` |
| arbitrary-index coordinate-face transport | `isDominant_coordinateFace_image_iff_ambient`, `isCell_coordinateFace_image_iff_ambient`, `isAssociatedSimplex_coordinateFace_image_iff_ambient` | `BeyondSperner.Freudenthal.Faces` |
| arbitrary-face ambient inclusion (`0 < N`) | `associatedComplex_subset_freudenthalComplex_of_pos`, `associatedComplex_subset_full_of_pos` | `BeyondSperner.Freudenthal.Faces`, `BeyondSperner.Freudenthal.Boundary` |
| Theorem 10.10 on the concrete Freudenthal--Scarf triangulation (`0 < N`) | `affinePointPosition_mem_referenceSimplex`, `affinePointPosition_injective`, `freudenthal_theorem10_10` | `BeyondSperner.Freudenthal.Applications.InwardTangent` |
| Appendix A.2 lexicographic extension | `OnePointExtension.IsLexicographicFor`, `exists_lexicographicExtension` | `BeyondSperner.OrientedMatroid.LexicographicExtension` |
| Lemmas 8.1--8.4 | declarations in `PerturbationSetup` | `BeyondSperner.Coloring.Matroid.General` |
| Theorem 8.5 | `MatroidColoring.theorem8_5` | `BeyondSperner.Coloring.Matroid.General` |
| generalized Scarf theorem | `GeneralizedScarf.generalizedScarf` | `BeyondSperner.Scarf.Generalized` |
| classical Scarf theorem and colorful cell | `ClassicalScarf.classicalScarf_odd`, `exists_colorfulCell` | `BeyondSperner.Scarf.Classical` |
| Lemma 3.1 and Scarf's Brouwer theorem | `ScarfBrouwer.envelope_coordDiameter_lt`, `scarf_brouwer_fixedPoint` | `BeyondSperner.FixedPoint.ScarfBrouwer` |
| Brouwer on an arbitrary finite affine simplex | `affineSimplexHomeomorphStandard`, `scarf_brouwer_fixedPoint_affineSimplex` | `BeyondSperner.FixedPoint.AffineBrouwer` |
| Lemmas 4.1--4.3 | `cyclicKey_lt_cyclicStep_of_ne`, `exists_pair_coord_ne_of_isCell`, `coord_range_of_isCell` | `BeyondSperner.Freudenthal.IntegerSimplex` |
| Lemma 4.6, finite-set equivalence | `image_prefixMap_stepSimplex`, `isFreudenthalTopSimplex_iff_cumulative` | `BeyondSperner.Freudenthal.IntegerSimplex`, `BeyondSperner.Freudenthal.Complex` |
| Lemma 4.7 | `coord_eq_zero_of_isCell_of_not_mem`, `coord_eq_zero_of_mem_associatedComplex_of_not_mem` | `BeyondSperner.Freudenthal.IntegerSimplex` |
| Lemma 4.7, exact complex-level face containment | `associatedFace_simplex_vertex_coord_zero`, `associatedFace_existsUnique_bundledSimplex` | `BeyondSperner.Freudenthal.Faces` |
| dimension-lowering coordinate-face equivalence | `zeroFaceEquiv`, `image_univ_insertZeroPoint` | `BeyondSperner.Freudenthal.Faces` |
| first-coordinate Freudenthal face equality (`0 < N`) | `lowerFreudenthalRelabeledToFace_eq_coordinateFace_zero` | `BeyondSperner.Freudenthal.Faces` |
| arbitrary-coordinate Freudenthal face equality (`0 < N`) | `lowerFreudenthalRelabeledToFace_eq_coordinateFace` | `BeyondSperner.Freudenthal.Faces` |
| arbitrary-coordinate Scarf face equality | `lowerScarfRelabeledToFace_eq_coordinateFace` | `BeyondSperner.Freudenthal.Faces` |
| injective chain transport and equation (21) | `mapChainHom_boundary`, `associatedFaceTopChain_eq_freudenthalCoordinateFaceChain_of_lower_eq` | `BeyondSperner.Simplicial.ChainSimplex`, `BeyondSperner.Freudenthal.Boundary` |
| equation (18), explicitly summed over coordinate faces | `boundary_associatedTopChain_eq_sum_associatedFaces` | `BeyondSperner.Freudenthal.Boundary` |
| formula (19), exact Freudenthal boundary | `boundary_freudenthalTopChain_eq_sum_coordinateFaces_of_pos` | `BeyondSperner.Freudenthal.Boundary` |
| equation (20), top-chain equality (`0 < N`) | `associatedTopChain_eq_freudenthalTopChain_of_pos` | `BeyondSperner.Freudenthal.Boundary` |
| Theorem 4.8, complex equality (`0 < N`) | `associatedComplex_eq_freudenthalComplex_of_pos` | `BeyondSperner.Freudenthal.Boundary` |
| Corollary 4.9, combinatorial full-facet equality (`0 < N`) | `fullCells_eq_freudenthalFacets_of_pos` | `BeyondSperner.Freudenthal.Boundary` |
| Corollary 4.9, geometric complexes and exact coverage (`0 < N`) | `gammaFreudenthalGeometricComplex_space_eq_realGamma`, `deltaFreudenthalGeometricComplex_space_eq_realDelta` | `BeyondSperner.Freudenthal.GeometricComplex` |
| Corollary 4.9, literal abstract/geometric face identification | `mem_deltaFreudenthalGeometricComplex_faces_iff_literal`, `image_realGammaToDelta_mem_delta_faces_iff` | `BeyondSperner.Freudenthal.GeometricComplex` |
| Corollary 4.9, paper's top-dimensional `I`-cell wording (`0 < N`) | `isCell_iff_realization_mem_delta_faces_and_card_of_pos` | `BeyondSperner.Freudenthal.GeometricComplex` |
| Corollary 4.10 (`0 < N`) | `isCell_univ_iff_exists_stepSimplex_of_pos` | `BeyondSperner.Freudenthal.Boundary` |
| order-preserving transport of associated complexes | `isDominant_image_iff`, `isCell_image_iff`, `associatedComplex_relabel` | `BeyondSperner.Orders.LinearOrders` |
| top-chain equality implies Theorem 4.8 complex equality | `associatedComplex_eq_freudenthalComplex_of_topChain_eq` | `BeyondSperner.Freudenthal.Complex` |

## Proof-obligation policy

- No `axiom` or `admit` declarations are permitted.
- `sorry`, `admit`, declared `axiom`, and any transitive dependency on `sorryAx` are prohibited in
  the published `BeyondSperner` tree.  `FormalizationInterface/AuditAll.lean` checks this over the
  complete namespace rather than relying only on a lexical source scan.
- Proof automation may prove lemmas or fill theorem bodies, but should not change a definition,
  structure field, or theorem hypothesis without a new semantic review.
- The dependency spine is now closed: the rank-two/coline construction of new-point-zero
  cocircuits is proved in `LexicographicSecondary`, and the exact circuit signing, primary lifts,
  orthogonal-pair recovery, one-point extension, full `IsLexicographicFor`, Lemmas 8.1--8.4,
  Theorem 8.5, and the final generalized-Scarf theorem are kernel-checked without `sorryAx`.

## Rethlas audits

- Lemma 7.3 has a one-iteration Rethlas proof with independent verifier verdict `correct`, no
  critical errors, and no reported gaps.  The preserved artifact is
  [`../Rethlas/BeyondSperner/Lemma7_3.verified.md`](../Rethlas/BeyondSperner/Lemma7_3.verified.md).
  It also independently recovers the
  empty-`X` counterexample, confirming that `[Nonempty X]` is semantically necessary.
- A Rethlas verdict is evidence about the informal proof blueprint, not a Lean proof.  For Lemma
  7.3 the blueprint has now also been translated into Lean; `#print axioms` confirms that the
  theorem does not depend on `sorryAx`.
- The prepared but never externally submitted lexicographic-extension input is
  [`../Rethlas/BeyondSperner/LexicographicExtension.problem.md`](../Rethlas/BeyondSperner/LexicographicExtension.problem.md).
  It explicitly forbids treating the cited Las Vergnas/Todd existence theorem as the proof and
  requires all new-point-zero secondary cocircuits to be handled.  That obligation has since been
  discharged directly in Lean; the prompt is retained only as an audit artifact.

## Semantic audit of the associated family

The article calls the complexes generated by the `A`-cells a simplex-family.  The literal stronger
reading “`T(A)` always has a simplex of cardinality `|A|`” is false for arbitrary order families:
if two indices carry the same order on a two-point set, Lemma 2.1 forces every nonempty dominant
set to have at most one element, so there is no two-element cell.  The Lean interface therefore
records the universally valid dimension upper bound.  It also inserts the empty simplex explicitly
when no `A`-cell exists, as required by `FiniteSimplicialComplex`.

## Scope of this milestone

The generalized-Scarf dependency spine (Sections 1, 2, 5, 6, the extended-order bridge of Section
7, Section 8, and the relevant appendices) and Section 3 are kernel-checked.  Section 4 now
contains both its arithmetic/order layer and the full-cell classification of Lemma 4.4 and
Theorem 4.5, together with the exact Freudenthal facet/top-chain definitions and the general
finite chain-uniqueness lemma used at the end of Theorem 4.8.  Every coordinate face is now
related to the lower-dimensional point type by an explicit equivalence, with induced/relabelled
complexes kept distinct, and chain relabeling is proved to commute with the `F₂` boundary.  For
every coordinate, the relabelled lower Freudenthal complex is proved equal to the induced
ambient face complex under the necessary hypothesis `0 < N`; the proof includes explicit,
separate facet lifts for the first, interior, and last coordinates, plus an unconditional reverse
collapse.  The corresponding Scarf face equality is
proved for every coordinate without a scale hypothesis, using exact cyclic-enumeration
naturality, cyclic-key deletion, and a monotone projection that handles dominance against all
ambient points.  Concrete non-branching is proved by intrinsic rank classification, including
  separate first-endpoint, interior, and last-endpoint completion bounds.  Strong facet-connectivity
is proved by explicit adjacent-swap paths, strict descent of cumulative base weight, and uniqueness
of the valid zero-base facet.  Formula (18) and the ambient chain-level formula (21) are proved.
The exact cofacet classification proves formula (19): coordinate-boundary faces have one cofacet,
whereas codimension-one faces with no common zero coordinate have two.  The top-chain induction,
equation (20), Theorem 4.8, and Corollary 4.10 are therefore proved for `0 < N`.  Corollary 4.9 is
proved both in its exact finite-combinatorial form and in its real-geometric form.  The latter
constructs actual geometric simplicial complexes on the monotone and standard simplices, proves
the face-intersection axiom and affine independence, proves exact coverage, and identifies every
geometric face with the realization of a face of the independently defined abstract complex.
The cumulative coordinate embedding is an explicit equivalence with the integral monotone
simplex, and its real affine counterpart carries and reflects the geometric faces.
Sections 7 and 9 are now covered through the vector Scarf theorem and the resulting Kakutani
fixed-point theorem.  Section 10 is covered through its `F₂` chain identities, normalized
arbitrary-map pushforward, the exact general-position/intersection definitions, Lemmas 10.1--10.4,
Theorem 10.5, Corollary 10.6, and the paper's forward intersection-number proofs of Lemma 10.7
and Theorem 10.8.
Lemma 10.4's exact-codimension-one case is proved directly from
affine-dependence coefficients rather than by the paper's hyperplane induction.  Corollary 10.6
has a separate dimension-zero proof because Lemma 10.2 necessarily assumes `0 < n`.  Also checked
are formula (40), the independent oriented-matroid proof of Theorem 10.8, Theorem 10.9, the envelope-covering conclusion of Lemma 10.7 derived
in the reverse direction from Theorem 10.8, and the algebraic/pure-complex form of Theorem 10.10.
The forward and reverse proofs of Lemma 10.7 are independent: the forward module imports only the
intersection chain and envelope infrastructure, not either Theorem 10.8 proof.  The paper-route
Theorem 10.8 continues from the forward lemma and is independent of the oriented-matroid theorem;
its adapter to formula (40) is kept in `FormalizationInterface`. For an arbitrary finite geometric
triangulation, the reference-face family, its exact geometric
coverage, dimension bound,
face-coordinate compatibility, ambient inclusion, finite facet extension, and the implication
from geometric facet cardinality to abstract purity are now constructed.  The general
local non-branching property and facet cardinality are both derived automatically from the minimal
finite geometric-triangulation data, and the resulting pseudo/chain implications are proved.
For the concrete positive-scale Freudenthal/associated complex, top-dimensional purity,
arbitrary-face compatibility, ambient inclusion, normalized affine realization, and the
resulting Theorems 10.9 and 10.10 are all proved.  The arbitrary finite geometric-triangulation
abstraction is also complete at this obligation layer.  Provider-parameterized proofs now route
both later theorems, the arbitrary geometric applications, and the Freudenthal applications
through either independent Theorem 10.8 proof.  Separately, barycentric coordinates now transport
the Section 3 Scarf--Brouwer theorem from the standard simplex to the convex hull of any finite
real affine basis.  Extending this to every nonempty compact convex subset remains a genuine scope
expansion, not discharge of any claim listed in this paragraph.
