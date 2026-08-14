# BeyondSperner formalization status

This file distinguishes three notions which must not be conflated:

1. **defined**: Lean accepts the structure or predicate and its types;
2. **kernel-proved**: `#print axioms` has no `sorryAx` in the declaration's transitive dependency
   closure;
3. **statement-only**: the intended declaration exists, but its proof or construction still uses
   `sorryAx`, directly or through a dependency.

The status below was last audited after proving Section 2 through Theorem 2.7 and Corollary 2.9,
Theorems 1.2, 1.5, 1.6, 6.5, 7.2, and the reduction in 8.5, Lemmas 6.1--6.4, 7.1, and 7.3, Todd's existence and
uniqueness proofs, Corollaries 8.3 and 8.4, the restriction/deletion construction for oriented
matroids, the finite Farkas/four-painting argument, signed-cocircuit elimination and involutive
oriented duality, the nondegeneracy of the deleted perturbation framework, and both
final-solution translations, and the complete lexicographic single-element extension.  The latter
now includes exact circuit signings, primary lifts, the strict secondary rank-two/coline
construction, exact orthogonal-pair assembly, and `IsLexicographicFor`.  The audit also includes
the finite proof that weak signed-circuit elimination implies strong elimination, after removing
strong elimination from the `Data` structure.
It now also covers the complete Section 3 Scarf--Brouwer route, its explicit transport from the
standard simplex to the convex hull of an arbitrary finite real affine basis, and the checked arithmetic/order
and full-cell-classification layers of Section 4: Lemmas 4.1--4.4 and 4.7, Theorem 4.5,
fixed-sum injectivity of the cumulative-coordinate map, and both finite-set directions of
Lemma 4.6.  The chain-level boundary induction, formula (19), Theorem 4.8, Corollary 4.10, and
both the combinatorial and full real-geometric forms of Corollary 4.9 are now kernel-proved for
`0 < N`.
The audit now also includes the realizable oriented matroid constructed from elementary real
dependences, all linear/oriented compatibility bridges, Theorem 7.2 with a literal linear-basis
conclusion, the final vector Scarf theorem including its direct raw-`φ` interface, the full
Section 9 Scarf route to Kakutani's theorem, and the checked Section 10 chain identities,
Lemmas 10.1--10.4, Theorem 10.5, Corollary 10.6, the forward intersection-number proofs of
Lemma 10.7 and Theorem 10.8, Lemma 10.3, formula (40), Theorems 10.8 and 10.9, the alternate envelope-covering proof
of Lemma 10.7 derived from Theorem 10.8 without general position, the centered algebraic/pure-complex form
of Theorem 10.10, and concrete positive-scale Freudenthal--Scarf instances of Theorems
10.9 and 10.10.  It now also includes the first general geometric-triangulation bridge: induced
reference-face complexes, their exact geometric coverage, dimension bounds and coordinate compatibility, exact conversion
between full abstract and geometric faces, finite facet extension, automatic abstract purity
from finite-dimensional topology and exact coverage, local top-coface existence, the universal
one-or-two upper classification, exact uniqueness on the reference boundary, the local crossing
argument giving two cofaces off the boundary, and hence automatic non-branching.

The mathematical source currently contains **no** `sorry`, `admit`, or declared `axiom`.
The representative transitive audit reports no `sorryAx`, including for
`exists_lexicographicExtension`, `exists_perturbationSetup`, Theorems 7.2 and 8.5, and both
generalized Scarf theorems; their remaining dependencies are the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`.

## Scope relative to the paper

The paper has Sections 1--10 and Appendices A.1--A.2.  `BeyondSperner` contains the dependency
spine for the generalized Scarf theorem together with the following expansion:

- kernel-checked coverage of the listed results in Sections 1, 2, 5, 6, and 8;
- the complete Section 3 Scarf--Brouwer argument, including the quantitative envelope estimate,
  compact finite nets, the limiting fixed-point proof, and the barycentric homeomorphism giving
  Brouwer on the convex hull of an arbitrary finite real affine basis;
- the arithmetic/order, full-cell-classification, and coordinate-change portion of Section 4
  through Lemmas 4.1--4.7, including Theorem 4.5 and the full finite-set equivalence of Lemma 4.6;
- the full vector-coloring development of Section 7: Lemma 7.1, the realizable oriented-matroid
  construction, Theorem 7.2, Lemma 7.3, and the final vector Scarf theorem;
- the Todd and constructed lexicographic-extension developments from Appendices A.1--A.2;
- the proved generalized Scarf theorem following Theorem 8.5;
- Section 9 through the Scarf--Kakutani fixed-point theorem;
- the Section 10 `F₂` chain identities and arbitrary-map normalized pushforward, the exact
  general-position/intersection definitions, Lemmas 10.1--10.4, Theorem 10.5, Corollary 10.6,
  the paper's forward intersection-number proofs of Lemma 10.7 and Theorem 10.8, Lemma 10.3,
  formula (40), Theorem 10.8 for an arbitrary real affine basis, the envelope-covering conclusion
  of Lemma 10.7 derived from Theorem 10.8 without general position, Theorem 10.9 under its exact
  face-compatibility obligation, Theorem 10.10 under explicit face-compatibility,
  ambient-inclusion, and top-dimensional purity obligations, and concrete positive-scale
  Freudenthal--Scarf instances in which those obligations are proved.

Section 10's chain/intersection route is kernel-proved through Theorem 10.8.  The exact
general-position predicates and intersection numbers are defined; Lemmas 10.1 and 10.2 include
the geometric exclusion of a singleton/tangential segment intersection and the finite-obstacle
escape argument.  Lemma 10.2 explicitly requires `0 < n`, because its printed dimension-zero
reading is false.  Lemma 10.4 is complete: Carathéodory handles affine dimension at most `n - 2`,
while affine-dependence coefficients prove the exact-codimension-one two-facet parity directly.
Theorem 10.5 is obtained by a separately proved bilinear support expansion.  Corollary 10.6 uses
it and Lemma 10.2 in positive dimension and has an independent dimension-zero base case.  The
forward proof of Lemma 10.7 now derives `∂ E[[I]] = ∂ I`, transports it through normalized
pushforward, applies Corollary 10.6 to the resulting cycle, and extracts an actual top envelope
simplex from a nonzero finite intersection sum.  Its module does not import either proof of
Theorem 10.8.  `BeyondSperner.Euclidean.Intersection.AffineColoring` then formalizes the paper's general-position
limit step: the complement of the finite small-affine-span locus is dense, every good interior
point is covered by a full-cardinality generic envelope simplex, and the finite union of those
closed convex hulls covers the closure of the reference-simplex interior.  The compatibility
adapter in `FormalizationInterface/Theorem10_8Intersection` converts this result exactly to
`IsAffineSolution`, independently of `AffineColoring.theorem10_8`.  The same Lemma 10.7 conclusion
is also kernel-proved in `BeyondSperner.Coloring.AffineEnvelope` from that oriented-matroid Theorem 10.8, with no
general-position assumption. The full local `GeometricTriangulation.IsNonbranching`
property is now derived from the minimal geometric coverage data: boundary codimension-one faces
have one top coface and non-boundary ones have two. Its implications to `IsPseudoSimplex` and
`IsChainSimplex`, as well as the induced family,
exact geometric coverage, dimension bound, face-coordinate condition, ambient inclusion, finite facet extension,
automatic full-dimensional facet cardinality, and purity are now checked.  Theorem 10.9 itself, including its finite-closed-
union boundary extension, is kernel-proved at the exact abstract obligation layer.  For the
concrete positive-scale Freudenthal complex, those obligations and both resulting top-simplex
theorems are kernel-proved.  Section 9 is kernel-proved,
including Lemma 9.1, the fixed-or-cell form of Lemma 9.2, equations (34)--(36), the
compactness/closed-graph limit, and Kakutani's theorem.  In Section 4,
formulas (18), (19), and (21), equation (20), Theorem 4.8, and Corollary 4.10 are kernel-proved for
`0 < N`.  Corollary 4.9 now has both its exact finite facet equality and a separate geometric
realization: genuine `Geometry.SimplicialComplex` structures are constructed on `Gamma` and
`Delta`, their faces are proved to be exactly the realized abstract Freudenthal faces, the affine
coordinate map carries and reflects faces, and their spaces are proved equal to the corresponding
real simplices.  Formula (19) is proved from the exact local classification: every coordinate-boundary
face has one cofacet, while every codimension-one face with no common zero coordinate has two.
The proof explicitly constructs the alternate endpoint rotation, decreased-base facet, or
adjacent-swap facet.  In particular, the current code does not call a family of
Freudenthal vertex sets a triangulation by definition.

## Checked core and completed proof bodies

| Area | What is actually checked |
| --- | --- |
| signed subsets | `SignedSubset`, support, negation, inclusion, empty signed set, erase, map/comap, injectivity of mapping, recovery after comap on the embedding range, signs, same/opposite sign, orthogonality, and the two-point orthogonality sign-transfer lemmas |
| oriented-matroid primitives | the signed-circuit `OrientedMatroid.Data` interface with weak elimination as its only elimination axiom; the finite contraction construction, support-minimal erased circuits, protected-coordinate Lemma 2.14, and the derived weak-to-strong theorem; elementary circuit/convexity consequences; the finite circuit cryptomorphism constructing the unique underlying ordinary matroid from unsigned circuit supports; basis agreement; signed fundamental circuits; an explicit fundamental-cocircuit construction proved to be a support-minimal covector; and the restriction/deletion construction |
| cocircuit duality | arbitrary-set deletion and contraction for orthogonal circuit/cocircuit pairs, the finite Farkas and four-painting alternatives, strong and weak signed-cocircuit elimination, the oriented dual whose circuits are precisely the original cocircuits, identification of its underlying ordinary matroid with the ordinary dual, and involutivity of oriented duality; none of these declarations assumes cocircuit elimination or depends on `sorryAx` |
| lexicographic localization data | the unique first supported list coordinate, the canonical signed lift to `α ⊕ Unit`, preservation of all old signs, injectivity, compatibility with negation, the exact criterion for the new coordinate to be supported, and equality of its sign with the first supported sign; these definitions and lemmas are kernel-proved, but they do not by themselves construct the oriented-matroid extension |
| ordinary principal extension | `PrincipalExtension.matroid` constructs the finite unsigned single-element principal extension directly from the independence axioms. Its augmentation proof, unchanged old-coordinate independence, bases, circuits, and closures, the exact spanning criterion for old sets, property A.2(a) at the unsigned cocircuit-support level, the converse classification for zero-new-coordinate supports disjoint from the principal set, and the bidirectional classification of all supports containing the new point are kernel-proved |
| lexicographic signed circuits | every ordinary extension circuit is assigned an explicit signing: old circuits are embedded and circuits containing `p` use priority-composed signed fundamental coefficients. Exact support, negation closure, coverage of every ordinary circuit support, and orthogonality to every primary `lexLift` are kernel-proved |
| secondary cocircuits and assembly | primary lifts cover every support containing `p`. `hasStrictSecondaryCocircuitSignings` proves the genuinely new `p = 0` case by closed-hyperplane/coline reduction, ordinary circuit elimination, Todd conformalization, exact support coverage, and orthogonality to every explicit circuit signing. The strict result implies the full `HasSecondaryCocircuitSignings`; the code then constructs an exact `OrthogonalPair`, recovers `Data`, proves the underlying matroid is the principal extension, constructs `OnePointExtension`, and proves `IsLexicographicFor` |
| simplex primitives | finite complexes including the empty face, simplex-families, dimension upper bounds, pseudo-simplex incidence counts, `F₂` chains and boundaries, Theorem 1.2 (`IsPseudoSimplex.isChainSimplex`), the envelope complex and dimension bound, and the two envelope preservation results (Theorems 1.5 and 1.6) |
| order primitives | indexed orders, dominance/cell/face predicates, Lemmas 2.1--2.6, Theorem 2.7, the associated complex/family including its empty face and dimension bound, Corollary 2.9, the concrete three-level extended orders, and exact invariance of dominance, cells, associated simplices, and associated complexes under simultaneous order-preserving equivalences of indices and vertices |
| classical Scarf and Brouwer | the canonical simplex oriented matroid, exact good-basis/color-cover equivalence, oddness and existence of a colorful cell, coordinate-refining cyclic orders, the quantitative envelope-diameter lemma, finite dense subsets obtained from compactness, close coordinate witnesses, and the continuous fixed-point limit theorem on the standard simplex; `BeyondSperner.FixedPoint.AffineBrouwer` additionally proves the barycentric-coordinate homeomorphism for an arbitrary finite real affine basis and transports the fixed point theorem to its convex hull |
| integer-simplex arithmetic | exact cyclic lexicographic orders; cyclic transfers; Lemma 4.1; the full-cardinality minimum-map argument for Lemma 4.2; the coordinate-range bound of Lemma 4.3; Lemma 4.7 for arbitrary `C`, both on a literal cell and on every vertex of its generated associated complex; fixed-sum injectivity and the monotone-simplex image of the prefix map; the explicit consecutive-difference inverse and equivalence `pointGammaEquiv` between `Point` and integral `Gamma`; preservation of total coordinate sum along every transfer sequence; transfer/prefix identities; and the exact image/cardinality calculations for permutation step simplices |
| integer-simplex cell classification | canonical increasing enumerations in every cyclic order; the minimum-map equivalence onto the cell; exact low/high coordinate blocks; invariance of directed cyclic edges under change of order; Lemma 4.4 with its rotation and two coordinate changes; proof that every remaining coordinate is unchanged; the induced permutation fixing zero; equality of the ordered vertex sequence with the transfer sequence; and Theorem 4.5 as an exact finite-set equality after the injective coordinate embedding |
| Freudenthal-complex and Theorem 4.8 | the full finite-set equivalence between original transfer simplices and cumulative-coordinate Freudenthal simplices (Lemma 4.6); an actual downward-closed finite complex generated by those facets contained in `Point N n`; proof that the existential step-simplex presentation is exactly the cardinality-`n+1` facet set; its explicit `F₂` top chain; and `freudenthalComplex_isPureOfCardinality_of_pos`, which extends every face, including the empty face, to a cardinality-`n+1` facet.  The general chain-uniqueness theorem is proved from purity, non-branching, strong facet-connectivity, and nonempty boundary; the intrinsic cumulative-rank classification handles every codimension-one face.  Concrete non-branching holds for `0 < n` and concrete strong facet-connectivity for all `N,n`.  The exact boundary classification proves one cofacet on coordinate faces and two elsewhere.  Consequently formula (19), equation (20), top-chain equality, equality of the Scarf and Freudenthal complexes, and purity of the full associated complex are proved for every `n` when `0 < N`. |
| geometric Corollary 4.9 | real `Delta` and monotone `Gamma`; exact affine coordinate changes and vertex compatibility; affine independence of every face; an explicit half-space/convex-hull description of each Freudenthal cell; canonical barycentric coordinates and a cell-independent global hat function; face-level convex-hull intersection; actual gamma and delta `Geometry.SimplicialComplex` structures; explicit boundary-aware cube coverage with the necessary reverse-index tie break; exact space equalities with `Gamma` and `Delta` for `0 < N`; and face-by-face identification with the independently defined abstract Freudenthal complex. |
| coordinate-face and chain transport | deletion of one index gives an explicit equivalence with the remaining-index subtype and its ambient image is exactly `I \ {k}`; insertion/deletion of a zero coordinate are inverse equivalences and their image is exactly the coordinate face; induced and relabelled face complexes are defined without identifying distinct vertex types; every simplex of `T(I \ {k})` has a unique bundled representative in that face complex; complex relabeling is invertible; and both equivalence relabeling and injective vertex pushforward are boundary-preserving chain maps.  Fixed-cardinality chains push through an induced subtype without losing or merging coefficients.  For every `k`, explicit lifting and collapsing of permutation-step simplices prove both Freudenthal-complex inclusions and exact face equality under `0 < N`; the reverse inclusion itself is unconditional.  Exact cyclic-enumeration naturality and ambient/face dominance prove the unconditional Scarf face equality.  At chain level, formula (18) is explicitly enumerated by `univ.erase k`, formula (21) is proved in the common ambient chain group, and formula (19) is proved coefficientwise from exact cofacet counts. |
| Theorem 4.8 base case | for `n = 0`, `Point N 0` is proved to consist of one explicit point; the Freudenthal facet set is the singleton containing that vertex; non-branching, strong facet-connectivity, nonempty boundary, the unique full-cell assertion, equality of the Scarf and Freudenthal complexes, and equality of their top chains are all kernel-proved |
| Lemma 7.3 | all extended-order comparison lemmas, exact `extendCell` membership lemmas, and `dominant_extendCell_iff`; its axiom closure is `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` |
| vector-coloring Lemma 7.1 | a finite injective vector configuration containing the standard basis and `b`, equation (29), equation (30) as the zero-extended coefficient space on `M - {b}`, the canonical solution, elimination of the `b` coefficient from a nonnegative dependence, preservation of nontriviality, and the resulting explicit unbounded ray |
| realizable oriented matroid | signed circuits defined as sign vectors of support-minimal nonzero real dependences; sign reversal, circuit incomparability, and weak elimination are proved. Oriented independence is equivalent to linear independence, the standard-basis range is an oriented-matroid basis, acyclicity is equivalent to absence of nonzero nonnegative dependence, and convex-hull membership outside the set is equivalent to a supported nonnegative linear representation. The protected-coordinate extraction used in the convex proof is explicit. |
| vector Theorem 7.2 and Scarf | boundedness and equation (29) construct a genuine `MatroidColoring.Framework`; Theorem 8.5 supplies the completed good basis; cardinality plus linear independence construct a `Module.Basis` indexed by the literal vector image; the convex bridge supplies a nonnegative coefficient function indexed by that same image and proves its finite sum is `b`. `VectorScarf.vectorScarf` then uses the checked associated-family theorem and Lemma 7.3 to obtain the final dominant set. `VectorScarf.RawData.scarf` starts from a literal `φ : X ⊕ I → ℝ^I`, proves its packaged vector map equals `φ`, and states the basis and coefficient conclusion directly on `S.image φ`. |
| Section 9 and Kakutani | `vectorColor` is the literal `f(x)-x+b`, and `vectorColor_eq_barycenter_iff` exposes the exact fixed-point exception. Lemma 9.1 derives coefficient bounds and boundedness from coordinate sums. Formula (34) is a literal vector image, equation (35) is reindexed by `I`, and Lemma 9.2 is the mathematically total fixed-stage-or-infinite-`C` alternative. Canonical finite dense samples, shrinking envelopes, one compact subsequence for base points/value selections/coefficients, closed graph passage, vanishing off `C`, and the coefficient calculation after (36) yield `scarf_kakutani_fixedPoint`. No pre-existing fixed-point theorem is used. |
| Section 10 chain, intersection, and affine layer | `boundary_boundary` proves `∂²=0` coefficientwise. `normalizedMapChainHom` is the paper's arbitrary-vertex-map pushforward: a collapsed simplex is zero, and the degenerate two-facet cancellation proves that it commutes with boundary. `EuclideanIntersection` defines general position using the paper's convex hulls (not stronger affine-span avoidance), proves exact face intersections for generic simplices, reduces a segment/simplex intersection to a compact parameter interval, excludes a singleton/tangential intersection, and proves Lemmas 10.1 and 10.2. `BeyondSperner.Euclidean.Intersection.DegenerateSimplex` proves the nongeneric case in full, with a direct affine-dependence/two-facet parity proof in exact codimension one. `chain_stokes_of_pairwise` isolates the bilinear algebra, `theorem10_5` performs the generic/nongeneric split, and `corollary10_6` includes a separate dimension-zero base case. `lemma10_7_intersection` implements the paper's forward envelope-cycle/intersection argument and returns a literal top envelope simplex; normalized-map degeneracy and finite-witness extraction are both explicit. `theorem10_8_envelope_intersection` proves the paper's next general-position/limit step through an equivalent finite-closed-union argument and retains both source and image cardinality. `theorem10_8_via_intersection` converts it exactly to formula (40). Provider-parameterized layers now thread this solution through Theorems 10.9 and 10.10: the latter reconstructs nonnegative convex weights from the public interface and proves every artificial basis weight is zero, rather than assuming the enriched coordinate witness. `lemma10_3_atMost` proves the affinely independent at-most-`m+1` Carathéodory form, and `lemma10_3` enlarges it to the paper's exact `m+1`-vertex face statement. Independently, `theorem10_8_coordinate` and `theorem10_8` provide the oriented-matroid route. `lemma10_7_envelope_of_theorem10_8` supplies an alternate reverse-direction covering proof without general position. |
| Theorem 10.9 | `theorem10_9_interior_of_solution_provider` isolates the cyclic proper-subset/closed-half-space argument from the source of Theorem 10.8. `theorem10_9_of_interior_provider` isolates the finite-closed-union boundary extension. Both the default theorem and `theorem10_9_via_intersection` instantiate these checked layers. The only geometric input is the explicit face-coordinate compatibility of vertices of `D(C)`. |
| Freudenthal Theorem 10.9 | `freudenthal_theorem10_9` supplies the face-coordinate compatibility from Lemma 4.7 and `affinePointPosition`; `freudenthal_theorem10_9_via_intersection` proves the same statement through the independent intersection route. Both retain only the literal vector-hedgehog condition, positive scale, and target membership. |
| general geometric triangulation bridge | `GeometricTriangulation.Data` stores only an actual geometric simplicial complex, finiteness of its vertex set, and exact coverage of the reference simplex. `faceComplex` and `family` construct the induced reference-face family; `faceComplex_card_le` derives the dimension bound from affine independence. Exact induced coverage, the full abstract/geometric face bridge, automatic purity, and local one-or-two coface incidence are proved. Thus `isNonbranching` supplies the pseudo/chain structure used by both default geometric applications and `geometric_theorem10_9_via_intersection`/`geometric_theorem10_10_via_intersection`; no pseudo/chain/purity/incidence conclusion is a field of `Data`. |
| Theorem 10.10 core | `barycentricCenter` and `centeredOutsideSum_basis` supply the centered functional. The original `theorem10_10_coordinate_core` consumes explicit coefficients. Independently, `zero_mem_colorHull_of_affineSolution` extracts weights from ordinary convex-hull membership in `IsAffineSolution`, proves their weighted centered sum is zero, and eliminates all strictly positive artificial basis terms. `theorem10_10_core_of_affineSolution` and `theorem10_10_of_core` separate provider choice from top-simplex extension; `theorem10_10_via_intersection` instantiates both. Ambient inclusion and purity remain genuine triangulation obligations, not consequences of `IsChainSimplex`. |
| Freudenthal Theorem 10.10 | arbitrary-index coordinate-face transport proves ambient inclusion, Theorem 4.8 supplies purity, and `affinePointPosition` plus Lemma 4.7 supplies face coordinates. Both `freudenthal_theorem10_10` and `freudenthal_theorem10_10_via_intersection` consequently have no face, inclusion, or purity assumptions. |
| coloring interfaces | `Framework`, nondegeneracy predicate, coloring/image/completed-image/solution predicates, the elementary proof that the distinguished basis is good, and complete proof bodies for Lemmas 6.1--6.4 and Theorem 6.5; the proof includes the `F₂` cochain evaluation, boundary normalization, and the envelope-top-simplex/solution-pair bijection |
| extension interfaces | the types `OnePointExtension`, `IsLexicographicFor`, and `PerturbationSetup`, cocircuit-lifting interfaces derived from the lexicographic specification, and the well-formed signed set `fundamentalCircuit` |
| perturbation consequences | both parts of Lemma 8.1 and all of Lemma 8.2 (existence, sign containment, and uniqueness), Corollaries 8.3 and 8.4, construction of the deleted framework and lifted coloring, nondegeneracy of the deleted framework, the completed-image embedding identity, and the good-basis transfer theorem are kernel-proved for an explicitly supplied `PerturbationSetup`; they do not themselves depend on `sorryAx` |
| final theorem | Theorem 8.5 is kernel-proved through the constructed perturbation setup, deleted nondegenerate framework, and Theorem 6.5; the generalized-Scarf theorem then performs the checked cell-to-final-solution translation and is also free of `sorryAx` |

Every row above was checked by the readable representative axiom audit.  In addition,
`FormalizationInterface/AuditAll.lean` enumerates every declaration whose fully qualified name is
under `BeyondSperner` (including declarations from the compatibility modules) and rejects declared
axioms, any transitive dependency on `sorryAx`, and every axiom outside `propext`,
`Classical.choice`, and `Quot.sound`.  At this revision it checks 3660 declarations.  This does not
assert that a chosen definition is the unique possible formalization of the paper, nor that a
theorem outside the stated scope has been formalized.

## Remaining `sorryAx`-tainted layers

None in the `BeyondSperner` mathematical module tree or in the audited dependency spine.

## Important surface-formalization warnings

- A structure whose proof fields are filled with `sorry` is not a completed construction.  At
  present none of `Envelope.complex`, `Envelope.family`, `associatedComplex`, `associatedFamily`,
  or `OrientedMatroid.Data.restrict` has this problem; all of their structure fields are proved.
- A declaration may contain no literal `sorry` and still be tainted transitively, so the audit
  checks dependency closures rather than source text alone.  The current audit confirms that the
  lexicographic extension, perturbation setup, Theorem 8.5, and generalized Scarf theorem are all
  free of `sorryAx`.
- `OnePointExtension`, `IsLexicographicFor`, and `PerturbationSetup` are specifications.
  `assembledLexExtension` is now an actual conditional construction, and
  `assembledLexExtension_isLexicographicFor` proves the full conditional specification, while
  `hasStrictSecondaryCocircuitSignings` and its reduction to `HasSecondaryCocircuitSignings`
  discharge that hypothesis. `exists_lexicographicExtension` and `exists_perturbationSetup` are
  therefore actual constructions, not specification-only declarations.
- Ivanov cites the Las Vergnas/Todd lexicographic-extension theorem in Appendix A.2 but does not
  prove it.  The Lean development does not use that cited existence result as a black box: the
  secondary `p = 0` signing is constructed in `OrientedMatroid/LexicographicSecondary.lean` from ordinary
  closure/circuit elimination and the already proved Todd circuit theorem, and its exact support
  and orthogonality are checked explicitly.
- `theorem6_5` is kernel-proved, including its oddness assertion.  Lemmas 8.1 and 8.2 are
  kernel-proved for any supplied setup, based on signed fundamental circuits/cocircuits,
  ordinary-matroid augmentation, and circuit--cocircuit orthogonality. `theorem8_5` has a complete
  Lean proof body: it builds the perturbation setup, applies Theorem 6.5 after deletion, and
  transfers the resulting good basis back.  Its dependency closure, and that of the final theorem,
  is now free of `sorryAx`.
- The displayed Scarf theorem on p. 41 suppresses hypotheses inherited from the vector framework.
  Its proof sets `M = φ(X ∪ I) + b` and applies Theorem 7.2, which requires the nonnegative
  solution set of equation (30) to be bounded, `b ∉ B`, and the restriction of `φ` to `X` to
  land in `M - b`.  `VectorScarf.RawData` records the last two requirements as `b_ne_basis` and
  `old_ne_b`; `RawData.scarf` takes boundedness explicitly.  Without these conditions, the
  printed unrestricted reading is not justified by that proof.
- The proof body of `VectorColoring.Framework.theorem7_2` is mathematically complete but does
  not reproduce the sequential perturbation argument printed in Section 7.  It factors through
  the stronger kernel-proved oriented-matroid Theorem 8.5 and then uses the realizability bridges
  to recover an actual linear basis and nonnegative coefficients.  There is no dependency cycle,
  but this is a deliberate proof-architecture divergence from the article.
- Section 9's printed invocation suppresses the case `c(x) = b`.  This is not harmless at the
  vector-coloring interface: it is exactly `f(x) = x`, while old colors are required to avoid
  `b`.  The checked proof restores the branch explicitly.  It likewise states Lemma 9.2 as
  “some stage is exactly fixed, or one `C` supports cells infinitely often”; deleting the first
  alternative would overstate what the preceding finite applications prove.
- Theorem 10.8 now has two dependency-independent checked proofs.  The older proof uses the
  general oriented-matroid coloring theorem after barycentric-coordinate homogenization.  The
  Euclidean chain/intersection files prove `∂²=0`, the genuinely non-injective normalized
  pushforward, the exact general-position geometry, Lemmas 10.1--10.4, Theorem 10.5, and
  Corollary 10.6.  Lemma 10.4 deliberately replaces the paper's hyperplane induction with a
  direct affine-dependence/two-facet parity proof, avoiding an unformalized affine-coordinate
  transport.  `BeyondSperner.Euclidean.Intersection.EnvelopeCoverage` now applies these results in the paper's forward
  proof and is dependency-independent of both Theorem 10.8 proofs.  The new
  `BeyondSperner.Euclidean.Intersection.AffineColoring` continues from that lemma using dense avoidance of finitely
  many small affine spans and an equivalent finite-closed-union version of the paper's
  sequence/constant-subsequence argument.  It explicitly preserves full image cardinality;
  affine independence alone would not rule out collapsed vertices.  The external compatibility
  adapter proves the exact existing `IsAffineSolution` statement.  `BeyondSperner.Coloring.AffineEnvelope` also proves the same
  covering conclusion from the independently checked Theorem 10.8 and labels that reversed
  dependency explicitly.  Thus there is no remaining proof-architecture gap at Theorem 10.8.
- Theorem 10.9 is not recorded as an interior-only statement.  The checked proof formalizes the
  cyclic basis shift and proper-face half-space contradiction, then separately proves that the
  union of full-simplex color hulls is a finite union of closed sets and that the reference simplex
  is the closure of its nonempty interior.  These stages are now provider-parameterized, and
  `theorem10_9_via_intersection` checks the full boundary conclusion using the paper-route
  Theorem 10.8.  Its abstract theorem still exposes the genuine face-coordinate condition;
  both the general geometric and Freudenthal applications discharge it for both proof routes.
- The checked `theorem10_10` proves the full coefficient-elimination and top-simplex argument for
  any chain-simplex family satisfying the exact face-compatibility, inclusion in `D(I)`, and purity
  properties of a triangulation.  `SimplexFamily` alone does not contain these properties, and
  `IsChainSimplex` does not imply them.  For the positive-scale Freudenthal--Scarf complex,
  `freudenthal_theorem10_10` now proves these properties from the cyclic orders, iterated
  coordinate-face extension, and normalized affine realization.  `BeyondSperner.Geometry.Triangulation.Core` now
  constructs the analogous induced family from an arbitrary finite geometric triangulation and
  proves its face coordinates, ambient inclusion, finite facet extension, and automatic purity
  from finite-dimensional topology and exact coverage. `BeyondSperner.Geometry.Triangulation.Nonbranching` additionally proves
  local coface existence, at most two cofaces, exactly one on the reference boundary, and exactly
  two away from it by a supporting-hyperplane/local-crossing argument.  Thus non-branching is
  derived rather than hidden in either application theorem's assumptions.  The paper-route
  compatibility proof does not assume the explicit coefficient package returned by
  `theorem10_8_coordinate`: `zero_mem_colorHull_of_affineSolution` reconstructs weights from
  `IsAffineSolution` convex-hull membership and proves all artificial basis weights vanish.
  Consequently Theorem 10.10 and both concrete application families are independently checked
  through the intersection route as well.
- Rethlas verification is an informal proof audit.  Only the Lemma 7.3 Rethlas blueprint has so far
  been translated into Lean and independently checked to have no `sorryAx`.  A precise input for
  the formerly open lexicographic-extension theorem is preserved under `Rethlas/BeyondSperner` as
  a historical local prompt, but it was not sent externally.  The completed Lean proof is the
  authoritative result.
- The paper's phrase that the cell complexes form a simplex-family cannot consistently mean that
  every `T(A)` contains an `A`-cell: two duplicate orders give an immediate counterexample.  The
  checked interface uses the valid cardinality upper bound and explicitly includes the empty face;
  it does not claim nonexistent cells.
- Lemma 6.3 is valid in the top-dimensional situation used by the paper.  Its Lean statement now
  explicitly assumes `D.card = Fintype.card I`; omitting this implicit context produced an
  over-strong surface statement for arbitrary finite `D`.
- The paper notes that deriving strong elimination from weak elimination is highly nontrivial and
  permits taking strong elimination as an additional axiom.  The repository no longer uses that
  shortcut: `OrientedMatroid.Data` has only weak elimination, while
  `OrientedMatroid/WeakStrongElimination.lean` proves the support-minimal contraction construction, the
  protected-coordinate contraction lemma, and the full finite weak-to-strong theorem.  All
  downstream uses of `Data.strongElimination` therefore invoke a theorem rather than a structure
  field.
- Section 4 is intentionally split into three layers: integer/cyclic arithmetic,
  cell classification, and the chain-level Freudenthal triangulation theorem.  The first two
  layers (plus Lemma 4.7 and both finite-set directions of Lemma 4.6) are complete.  The general
  finite chain-uniqueness step used in Theorem 4.8 is proved, and its concrete Freudenthal
  hypotheses are discharged: non-branching by intrinsic rank classification, strong connectivity
  by an explicit global adjacency path, and nonempty boundary by a concrete boundary face.
  Formula (19) follows from the exact one-versus-two cofacet classification.  Together with
  formulas (18) and (21), this closes the top-chain induction and Theorem 4.8 for `0 < N`.
  The complete `n = 0` induction base is proved separately.  Definitions `stepSimplex` and
  `freudenthalSimplex` still name finite vertex sets only; the triangulation conclusion is a
  theorem about the resulting complexes, not part of those definitions.
- Scale zero must be separated explicitly: for `0 < n`, `freudenthalFacets 0 n` is proved empty,
  so the nonempty-boundary premise needed by the chain-uniqueness argument is false.  Any concrete
  positive-dimensional proof that uses this `n`-chain argument must therefore assume `0 < N`;
  an all-`N` complex-equality statement could instead prove the collapsed `N = 0` case separately
  (and the case `n = 0` is separately nondegenerate).
- The paper's phrase “identify a coordinate face with the lower-dimensional simplex” is not used
  as definitional equality.  `zeroFaceEquiv` proves the point-level bijection, while
  `lowerFreudenthalRelabeledToFace`, `freudenthalCoordinateFaceComplex`, and
  `scarfCoordinateFaceComplex` keep the complex-level claims explicit.  The Freudenthal equality
  is now proved for every `k` under `0 < N` by genuine facet lifts and a genuine reverse collapse.
  It is not generalized by assuming an unproved coordinate-permutation invariance: the first,
  interior, and last coordinates use distinct checked transfer constructions.  The Scarf equality
  is proved for every coordinate `k` without a scale
  hypothesis.  Its proof establishes the exact cyclic-enumeration identity after deleting `k`
  and explicitly projects arbitrary ambient test points to `x_k = 0` before using face dominance,
  so it does not replace ambient quantification by face quantification.  This is strictly stronger
  than Lemma 4.7's vertex-containment conclusion.  Generic order-preserving transport of
  associated complexes, injective pushforward of chains, and formula (21) itself are now proved.
  Formula (18) is also expanded as the sum over all erased coordinates.  Formula (19) is proved
  coefficientwise from the exact parity classification of Freudenthal codimension-one cofaces,
  and the resulting positive-scale induction proves equation (20) and Theorem 4.8.

## Recommended next expansion

The geometric upgrade of Corollary 4.9, the vector-coloring development of Section 7, the
Scarf--Kakutani development of Section 9, and Theorems 10.8--10.10 at their stated obligation
layers are now complete.  The independent intersection-number route is complete through
Theorems 10.8--10.10, including the general-position limit, exact formula-(40) interface,
provider-parameterized 10.9 boundary extension, and coefficient reconstruction needed by 10.10.
The affine-simplex Brouwer transfer is now complete: `BeyondSperner.FixedPoint.AffineBrouwer` constructs both directions of
the barycentric-coordinate homeomorphism, proves their inverse and continuity laws, and conjugates
the Section 3 fixed-point theorem without invoking a library Brouwer theorem.  This conclusion is
for the convex hull of an affine basis.  The next genuinely stronger expansion would be Brouwer
for an arbitrary nonempty compact convex subset of a finite-dimensional real normed space; another
architectural refinement would reproduce Section 7's printed
sequential perturbation proof instead of the current stronger oriented-matroid route. The local
`IsNonbranching` property for the arbitrary finite
geometric-triangulation family is now complete; the checked Section 4 triangulation remains
available for a separate general Brouwer route.

The code does not obtain geometric coverage merely by naming a collection of finite vertex sets a
triangulation: affine independence, downward closure, exact face intersection, and coverage are
separate kernel-checked theorems.  It also states the Section 4 induction under `0 < N`:
for positive dimension the scale-zero Freudenthal facet set is empty, so silently dropping this
hypothesis would be mathematically false for the present definitions.

The exhaustive and readable transitive audits can be reproduced with:

```bash
lake env lean FormalizationInterface/AuditAll.lean
lake env lean FormalizationInterface/Audit.lean
```
