# Historical Rethlas input: secondary cocircuits for a finite lexicographic extension

Status: prepared locally and never submitted to the external Rethlas generator/verifier.  The
target has since been proved directly in Lean in
`BeyondSperner/OrientedMatroid/LexicographicSecondary.lean`; this file is retained as an audit
artifact recording the original proof obligation.

Let `E` be finite, let `M` be an oriented matroid on `E` presented by signed circuits, and let
`A = (a₁, ..., aₖ)` be an ordered list of distinct elements whose underlying set is independent.
At the time this prompt was prepared, the local Lean development had reduced construction of the
lexicographic extension on `E ⊔ {p}` to the following statement:

> For every ordinary cocircuit support `K` of the finite principal extension such that `p ∉ K`,
> there is a signed subset `D` with `support(D) = K` which is orthogonal to every signed circuit
> in the already constructed set `lexSignedCircuits M A`.

In Lean the broad proposition is
`OrientedMatroid.HasSecondaryCocircuitSignings M order hindep`.  The proof isolates the genuinely
new case as `HasStrictSecondaryCocircuitSignings`, proves it as
`hasStrictSecondaryCocircuitSignings`, and then applies
`HasStrictSecondaryCocircuitSignings.toHasSecondary`.

Prove this statement without assuming lexicographic-extension existence.  The intended rank-two
route is to identify `E \ K` as the old coline associated with a hyperplane containing `p`, pass
to the corresponding rank-two contraction, locate adjacent old cocircuits whose lexicographic
localization signs are opposite, and eliminate the new coordinate to obtain the compatible
`p = 0` signing.

Once this statement is proved, the checked local assembly gives an oriented matroid `M'` such that:

1. signed circuits supported on `E` are exactly those of `M`;
2. `M'` has the same rank as `M`;
3. an old signed cocircuit disjoint from the list remains a cocircuit with value zero at `p`;
4. the cocircuits containing `p` are exactly the canonical lifts of old cocircuits meeting the
   list, where the sign at `p` is the sign at the first supported list coordinate.

The proof must explicitly account for all cocircuits on which `p` is zero. They are not in general
only the old cocircuits disjoint from `A`: secondary cocircuits can arise by eliminating `p` from
two primary lifts having opposite signs at `p`. A purported complete cocircuit system consisting
only of the primary lifts is invalid.

Do not use the Las Vergnas/Todd lexicographic-extension existence theorem as a black box; it is the
target. A general single-element-localization theorem may be used only if its construction, the
complete primary/secondary cocircuit description, and the verification of the oriented-matroid
axioms are expanded in the blueprint.

The blueprint for the remaining statement must separate and prove:

- the ordinary rank/codimension-two description of every `p = 0` cocircuit support;
- the required rank-two cocircuit adjacency or cyclic-order lemma;
- the sign change of the lexicographic localization along the relevant rank-two cocircuit path;
- construction of the secondary signed cocircuit and its exact support;
- orthogonality of that signing to both embedded old circuits and every new
  `lexCircuit` candidate.

## Kernel-checked starting point

The local Lean development already supplies, without `sorryAx`:

- signed subsets, orthogonality, circuit and cocircuit elimination, oriented duality;
- recovery of an oriented matroid from an exact orthogonal signing of all ordinary circuit and
  cocircuit supports;
- the canonical `lexLift`, including restriction to old coordinates, injectivity, negation,
  support at `p`, and the first-supported sign rule;
- the finite ordinary principal extension on `E ⊔ {p}` defined by
  `I independent ↔ oldPart(I) independent ∧ (p ∈ I → A ⊄ closure(oldPart(I)))`;
- preservation of old independence, bases, circuits, closure, and spanning;
- the unsigned A.2(a) implication for cocircuit supports;
- the exact unsigned equivalence
  `insert p (image K) is a cocircuit of the extension ↔ K is an old cocircuit ∧ K ∩ A is nonempty`;
- the converse that every extension cocircuit support containing `p` restricts to such a `K`.
- an explicit signing `lexCircuit M order B` for every ordinary circuit containing `p`, with
  support exactly `insert p (image B)`;
- an exact signed-circuit set covering every ordinary circuit support, closed under negation;
- orthogonality of every such circuit to every primary `lexLift` cocircuit;
- exact coverage of every ordinary cocircuit support containing `p` by a primary lift;
- conditional construction of an `OrthogonalPair`, recovery of `Data`, equality of its derived
  underlying matroid with the principal extension, construction of `OnePointExtension`, and a
  complete proof of `IsLexicographicFor`, all assuming only
  `HasSecondaryCocircuitSignings`.

The completed proof uses closed complements of cocircuits, a rank-free two-hyperplane circuit
elimination argument, Todd elimination to obtain conformal old cocircuits with opposite
localization signs, and an explicit orthogonality proof for their composition.  No Rethlas output
was used as a Lean proof or as a new axiom.

## Source scope

Ivanov, arXiv:2207.10832v1, Appendix A.2, states the desired existence and uniqueness and cites
Las Vergnas and Todd, but does not prove it. The citation is context, not an expanded proof.
