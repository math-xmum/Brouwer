# Rethlas audit: BeyondSperner Lemma 7.3

This is the preserved result of a one-iteration Rethlas generation-and-verification trial for
`IndexedLinearOrders.dominant_extendCell_iff`.

## Run metadata

- Rethlas commit: `887cc46427636bbdd235160a112f9a30ae81d040`
- model: `gpt-5.6-sol`
- reasoning effort: `max`
- iterations: `1`
- elapsed time: `00:13:43`
- verifier verdict: `correct`
- verifier critical errors: none
- verifier gaps: none

The Rethlas verifier summarized the result as follows:

> The proof is correct. The three comparison facts follow from the extended-order construction;
> the old-point witness equivalence correctly forces exactly the indices in `C`; formal points
> always have their own index as a witness; both directions of the dominance equivalence follow
> with the required nonempty-index conditions; and the `X = ∅` singleton-index example validly
> shows that nonemptiness of `X` is necessary under the stated convention.

This artifact is an informal mathematical verification.  Its blueprint has since been translated
into Lean: the corresponding theorem and all order-comparison lemmas are kernel-checked and their
axiom audit contains no `sorryAx`.

## Verified proof blueprint

### Extended-order comparisons

Let `i,j ∈ I` and let `a,b ∈ X` be old points. Then:

1. `i* ≤'_i z` for every `z ∈ X ⊔ I`;
2. `a ≤'_i b` if and only if `a ≤_i b`;
3. if `j ≠ i`, then `a ≤'_i j*`;
4. `a ≰'_i i*`.

The first three assertions are exactly the three levels in the definition of `≤'_i`: `i*` is
first, the old points form the middle level in their original order, and all `j*` with `j ≠ i`
form the last level.

For the fourth assertion, the first one gives `i* ≤'_i a`. If also `a ≤'_i i*`, antisymmetry of
`≤'_i` would give `a = i*`, which is impossible because the union is disjoint and `a` is old.

### Old-point witness equivalence

For every old point `y ∈ X`, every `τ ⊆ X`, and every `C ⊆ I`,

```text
(∃ i ∈ I, ∀ z ∈ E(τ,C), y ≤'_i z)
    ↔
(∃ i ∈ C, ∀ x ∈ τ, y ≤_i x).
```

Suppose first that `i ∈ I` witnesses the left-hand side. If `i ∉ C`, then
`i* ∈ E(τ,C)`, so the witness property gives `y ≤'_i i*`, contradicting comparison (4).
Hence `i ∈ C`. For every `x ∈ τ`, the old point `x` belongs to `E(τ,C)`, so `y ≤'_i x`;
comparison (2) gives `y ≤_i x`. Thus the same `i` witnesses the right-hand side.

Conversely, suppose that `i ∈ C` witnesses the right-hand side and take `z ∈ E(τ,C)`. If `z` is
old, then `z = x` for some `x ∈ τ`, so `y ≤_i x` and hence `y ≤'_i z`. If `z = j*` is formal,
then `j ∈ I \ C`; since `i ∈ C`, we have `j ≠ i`, and comparison (3) gives `y ≤'_i j*`.
Thus `i` witnesses the left-hand side.

### Formal-point witness

For every `j ∈ I`, take the order indexed by `i = j`. Since `j*` is least in `≤'_j`,

```text
∀ z ∈ E(τ,C), j* ≤'_j z.
```

### Dominance equivalence

Assume first that `E(τ,C)` is dominant with respect to `I`. Since `X` is nonempty, choose
`y₀ ∈ X`. Extended dominance gives an `i ∈ I` below every element of `E(τ,C)` from `y₀`.
The old-point witness equivalence turns this into a witness `i ∈ C`; in particular `C` is
nonempty. Applying the same equivalence to every `y ∈ X` gives exactly that `τ` is dominant with
respect to `C`.

Conversely, assume that `τ` is dominant with respect to `C`. Then `C` and hence `I` are nonempty.
For an old point `y`, take its original witness in `C` and use the old-point witness equivalence.
For a formal point `j*`, use the order indexed by `j`. Therefore every point of `X ⊔ I` has a
witness in `I`, so `E(τ,C)` is dominant with respect to all of `I`.

### Necessity of `Nonempty X`

Remove the nonemptiness hypothesis and take:

```text
X = ∅,    I = {i},    τ = ∅,    C = ∅.
```

Then `E(∅,∅) = {i*}` is dominant with respect to `I`: the index set is nonempty and the only test
point satisfies `i* ≤'_i i*`. But `τ = ∅` is not dominant with respect to `C = ∅`, because the
definition explicitly requires the indexing set to be nonempty. Hence the equivalence fails when
`X` is empty.
