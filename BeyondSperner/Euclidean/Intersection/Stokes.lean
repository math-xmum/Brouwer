import BeyondSperner.Euclidean.Intersection.DegenerateSimplex

/-!
# The chain-level intersection identity of Theorem 10.5

The geometric work is simplex-local: Lemmas 10.1 and 10.4 prove the
boundary/intersection identity for one `n`-simplex and one edge.  This file
keeps the remaining algebra explicit.  The first theorem is the exact
bilinear extension principle for finite `F₂`-chains; Theorem 10.5 then
discharges its pairwise premise by splitting on affine independence.
-/

namespace BeyondSperner
namespace EuclideanIntersection

open Classical
open SimplexFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [FiniteDimensional ℝ E] in
/-- A simplexwise boundary/intersection identity extends to arbitrary
finite `F₂`-chains by bilinearity.  Keeping the support premise explicit is
important: it says exactly which basis pairs have to be checked, and does
not smuggle any geometric statement into the chain algebra. -/
theorem chain_stokes_of_pairwise
    (c d : Chain E)
    (hpair : ∀ sigma ∈ c.support, ∀ omega ∈ d.support,
      oneChainIntersection (boundary (singletonChain sigma))
          (singletonChain omega) =
        pointChainIntersection (singletonChain sigma)
          (boundary (singletonChain omega))) :
    oneChainIntersection (boundary c) d =
      pointChainIntersection c (boundary d) := by
  induction c using Finsupp.induction generalizing d with
  | zero => simp [oneChainIntersection, pointChainIntersection]
  | single_add sigma a c hsigma ha ih =>
      have haOne : a = 1 := by
        apply ZMod.val_injective 2
        have hapos : 0 < a.val := by
          by_contra hnot
          have hzeroVal : a.val = 0 := by omega
          apply ha
          apply ZMod.val_injective 2
          simp [hzeroVal]
        have halt := ZMod.val_lt a
        have haval : a.val = 1 := by omega
        exact haval.trans (ZMod.val_one 2).symm
      subst a
      change oneChainIntersection
          (boundary (singletonChain sigma + c)) d =
        pointChainIntersection (singletonChain sigma + c) (boundary d)
      rw [boundary_add]
      change chainPairing faceOneSimplexIntersectionNumber
          (boundary (singletonChain sigma) + boundary c) d =
        chainPairing pointSimplexIntersectionNumber
          (singletonChain sigma + c) (boundary d)
      rw [chainPairing_add_left, chainPairing_add_left]
      congr 1
      · induction d using Finsupp.induction with
        | zero => simp
        | single_add omega b d homega hb ihd =>
            have hbOne : b = 1 := by
              apply ZMod.val_injective 2
              have hbpos : 0 < b.val := by
                by_contra hnot
                have hzeroVal : b.val = 0 := by omega
                apply hb
                apply ZMod.val_injective 2
                simp [hzeroVal]
              have hblt := ZMod.val_lt b
              have hbval : b.val = 1 := by omega
              exact hbval.trans (ZMod.val_one 2).symm
            subst b
            change oneChainIntersection (boundary (singletonChain sigma))
                (singletonChain omega + d) =
              pointChainIntersection (singletonChain sigma)
                (boundary (singletonChain omega + d))
            rw [boundary_add]
            change chainPairing faceOneSimplexIntersectionNumber
                (boundary (singletonChain sigma))
                (singletonChain omega + d) =
              chainPairing pointSimplexIntersectionNumber
                (singletonChain sigma)
                (boundary (singletonChain omega) + boundary d)
            rw [chainPairing_add_right, chainPairing_add_right]
            congr 1
            · apply hpair sigma
              · have hc0 : c sigma = 0 := by
                  by_contra hc
                  exact hsigma (Finsupp.mem_support_iff.mpr hc)
                simp [hc0]
              · have hd0 : d omega = 0 := by
                  by_contra hd
                  exact homega (Finsupp.mem_support_iff.mpr hd)
                simp [hd0]
            · apply ihd
              intro sigma' hsigma' omega' homega'
              apply hpair sigma'
              · exact hsigma'
              · rw [Finsupp.mem_support_iff]
                have hdne : d omega' ≠ 0 :=
                  Finsupp.mem_support_iff.mp homega'
                have hne : omega' ≠ omega := by
                  intro h
                  subst omega'
                  exact homega homega'
                simp [hne, hdne]
      · apply ih
        intro sigma' hsigma' omega homega
        apply hpair sigma'
        · rw [Finsupp.mem_support_iff]
          have hcne : c sigma' ≠ 0 :=
            Finsupp.mem_support_iff.mp hsigma'
          have hne : sigma' ≠ sigma := by
            intro h
            subst sigma'
            exact hsigma hsigma'
          simp [hne, hcne]
        · exact homega

/-- Theorem 10.5: for an `n`-chain and a one-chain in the paper's exact
general position, intersection with the boundary may be transferred from
the left chain to the right chain. -/
theorem theorem10_5
    (n : ℕ) (c d : Chain E)
    (hdim : Module.finrank ℝ E = n)
    (hgp : OneChainsInGeneralPosition n c d) :
    oneChainIntersection (boundary c) d =
      pointChainIntersection c (boundary d) := by
  apply chain_stokes_of_pairwise c d
  intro sigma hsigma omega homega
  have hsigmaM : IsMSimplex n sigma := hgp.1 sigma hsigma
  have hpairGP : OneSimplexInGeneralPosition sigma omega :=
    hgp.2.2 sigma hsigma omega homega
  by_cases hgeneric : IsGeneric sigma
  · exact lemma10_1 n sigma omega hdim hsigmaM hgeneric hpairGP
  · have hzero := lemma10_4 n sigma omega hdim hsigmaM hgeneric hpairGP
    exact hzero.1.trans hzero.2.symm

/-- In a zero-dimensional real vector space, a homogeneous zero-chain with
zero boundary is itself zero.  This is the missing base case in the paper's
proof of Corollary 10.6: Lemma 10.2 cannot be invoked in dimension zero
because no one-simplex exists there. -/
theorem zero_chain_eq_zero_of_boundary_eq_zero
    (c : Chain E) (hc : IsMChain 0 c)
    (hdim : Module.finrank ℝ E = 0) (hcycle : boundary c = 0) :
    c = 0 := by
  let : Subsingleton E := Module.finrank_zero_iff.mp hdim
  by_cases hsupp : c.support.Nonempty
  · obtain ⟨sigma, hsigma⟩ := hsupp
    have hcard : sigma.card = 1 := by
      simpa [IsMChain] using hc sigma hsigma
    have hsupportEq : c.support = {sigma} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hsigma, ?_⟩
      intro tau htau
      have htauCard : tau.card = 1 := by
        simpa [IsMChain] using hc tau htau
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
      obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp htauCard
      exact Finset.singleton_inj.mpr (Subsingleton.elim y x)
    have hcoeff : c sigma = 1 := by
      have hne : c sigma ≠ 0 := Finsupp.mem_support_iff.mp hsigma
      apply ZMod.val_injective 2
      have hpos : 0 < (c sigma).val := by
        by_contra hnot
        have hz : (c sigma).val = 0 := by omega
        apply hne
        apply ZMod.val_injective 2
        simp [hz]
      have hlt := ZMod.val_lt (c sigma)
      have hval : (c sigma).val = 1 := by omega
      exact hval.trans (ZMod.val_one 2).symm
    have hcEq : c = singletonChain sigma := by
      ext tau
      by_cases htau : tau = sigma
      · subst tau
        simp [singletonChain, hcoeff]
      · have htauNot : tau ∉ c.support := by
          simp [hsupportEq, htau]
        have hzero : c tau = 0 := by
          by_contra hne
          exact htauNot (Finsupp.mem_support_iff.mpr hne)
        simp [singletonChain, htau, hzero]
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
    subst c
    have hboundaryEmpty :=
      congrArg (fun chain : Chain E ↦ chain ∅) hcycle
    simp [boundary, boundaryHom, boundarySimplex, singletonChain] at hboundaryEmpty
  · have hempty : c.support = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hsupp
    exact Finsupp.support_eq_empty.mp hempty

/-- Corollary 10.6, including the dimension-zero base case omitted by the
paper's proof: a top-dimensional cycle has zero point-intersection number at
every point in general position with respect to the chain. -/
theorem corollary10_6
    (n : ℕ) (c : Chain E)
    (hdim : Module.finrank ℝ E = n)
    (hc : IsMChain n c) (hcycle : boundary c = 0)
    (z : E) (hz : PointInGeneralPositionWithChain c z) :
    pointChainIntersection c (singletonChain {z}) = 0 := by
  by_cases hn : 0 < n
  · apply lemma10_2 n c hdim hn hc
    · intro omega homega
      have hchains :
          OneChainsInGeneralPosition n c (singletonChain omega) :=
        (oneChainsInGeneralPosition_singleton_iff n c omega).2
          ⟨hc, homega⟩
      have hstokes := theorem10_5 n c (singletonChain omega) hdim hchains
      simpa [hcycle, oneChainIntersection] using hstokes.symm
    · exact hz
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hdim0 : Module.finrank ℝ E = 0 := hdim.trans hn0
    have hcZero : IsMChain 0 c := by simpa [hn0] using hc
    have hc0 :=
      zero_chain_eq_zero_of_boundary_eq_zero c hcZero hdim0 hcycle
    subst c
    simp [pointChainIntersection]

end EuclideanIntersection
end BeyondSperner
