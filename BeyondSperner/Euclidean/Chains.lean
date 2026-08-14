import BeyondSperner.Simplicial.ChainSimplex

/-!
# Finite `F₂` chains and pushforward for Section 10

This file supplies the combinatorial chain layer used at the start of
Section 10 of Ivanov's *Beyond Sperner's Lemma*.

The existing injective pushforward in `ChainSimplex` is not enough here:
the map from abstract vertices to Euclidean points may identify vertices.
Following the paper, an image simplex is therefore set to zero exactly when
the vertex map is not injective on that simplex.  The main theorem proves
that this normalized pushforward still commutes with the boundary.
-/

namespace BeyondSperner
namespace SimplexFamily

open Classical

variable {V : Type*} [DecidableEq V]
/-- The boundary of a simplex has zero boundary.  Coefficientwise, a
codimension-two face occurs exactly twice and hence cancels over `F₂`. -/
theorem boundary_boundary_singletonChain (sigma : Finset V) :
    boundary (boundary (singletonChain sigma)) = 0 := by
  ext tau
  rw [boundary_singletonChain, boundarySimplex]
  change boundaryHom (∑ v ∈ sigma, singletonChain (sigma.erase v)) tau = 0
  simp only [map_sum, boundaryHom_singletonChain]
  rw [show (∑ x ∈ sigma, boundarySimplex (sigma.erase x)) tau =
      ∑ x ∈ sigma, boundarySimplex (sigma.erase x) tau by
    exact map_sum (Finsupp.applyAddHom tau : Chain V →+ ZMod 2) _ _]
  simp_rw [boundarySimplex_apply]
  rw [Finset.sum_boole]
  by_cases h : tau ⊆ sigma ∧ tau.card + 2 = sigma.card
  · have hfilter : sigma.filter (fun x ↦
        tau ⊆ sigma.erase x ∧ tau.card + 1 = (sigma.erase x).card) =
        sigma \ tau := by
      ext x
      constructor
      · intro hx
        have hxData := Finset.mem_filter.mp hx
        refine Finset.mem_sdiff.mpr ⟨hxData.1, ?_⟩
        intro hxTau
        exact (by simpa using hxData.2.1 hxTau)
      · intro hx
        have hxData := Finset.mem_sdiff.mp hx
        apply Finset.mem_filter.mpr
        refine ⟨hxData.1, ?_, ?_⟩
        · intro y hyTau
          exact Finset.mem_erase.mpr ⟨fun hyx ↦ hxData.2 (hyx ▸ hyTau), h.1 hyTau⟩
        · rw [Finset.card_erase_of_mem hxData.1]
          omega
    rw [hfilter]
    have : (sigma \ tau).card = 2 := by
      rw [Finset.card_sdiff_of_subset h.1]
      omega
    rw [this]
    exact CharTwo.two_eq_zero
  · have hfilter : sigma.filter (fun x ↦
        tau ⊆ sigma.erase x ∧ tau.card + 1 = (sigma.erase x).card) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxData := Finset.mem_filter.mp hx
      apply h
      constructor
      · exact hxData.2.1.trans (Finset.erase_subset x sigma)
      · rw [Finset.card_erase_of_mem hxData.1] at hxData
        omega
    rw [hfilter]
    simp

/-- The chain identity `∂² = 0` from Section 10. -/
theorem boundary_boundary (c : Chain V) : boundary (boundary c) = 0 := by
  induction c using Finsupp.induction with
  | zero => simp
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
      change boundary (boundary (singletonChain sigma + c)) = 0
      rw [boundary_add, boundary_add, boundary_boundary_singletonChain, ih]
      simp

variable {W : Type*} [DecidableEq W]

/-- Image of one abstract simplex under an arbitrary vertex map.  A
nondegenerate simplex is sent to its image, while a simplex on which the map
identifies two vertices is sent to zero, exactly as in Section 10. -/
noncomputable def normalizedMapSimplex (f : V → W) (sigma : Finset V) : Chain W :=
  if (sigma.image f).card = sigma.card then singletonChain (sigma.image f) else 0

/-- The normalized pushforward `φ_*` of Section 10, extended additively to
all finite `F₂`-chains. -/
noncomputable def normalizedMapChainHom (f : V → W) : Chain V →+ Chain W :=
  Finsupp.liftAddHom fun sigma ↦
    { toFun := fun a ↦ a • normalizedMapSimplex f sigma
      map_zero' := zero_smul _ _
      map_add' := fun a b ↦ add_smul a b _ }

@[simp] theorem normalizedMapChainHom_singleton (f : V → W) (sigma : Finset V) :
    normalizedMapChainHom f (singletonChain sigma) = normalizedMapSimplex f sigma := by
  simp [normalizedMapChainHom, normalizedMapSimplex, singletonChain]

omit [DecidableEq V] in theorem normalizedMapSimplex_eq_of_injOn (f : V → W) (sigma : Finset V)
    (hf : Set.InjOn f sigma) :
    normalizedMapSimplex f sigma = singletonChain (sigma.image f) := by
  rw [normalizedMapSimplex, if_pos]
  exact Finset.card_image_iff.mpr hf

omit [DecidableEq V] in theorem normalizedMapSimplex_eq_zero_of_not_injOn (f : V → W) (sigma : Finset V)
    (hf : ¬ Set.InjOn f sigma) : normalizedMapSimplex f sigma = 0 := by
  rw [normalizedMapSimplex, if_neg]
  exact fun h ↦ hf (Finset.card_image_iff.mp h)

/-- Every vertex of every simplex surviving normalized pushforward lies in
the image of the original vertex type.  This remains true after cancellations
between equal image simplices. -/
theorem normalizedMapChainHom_support_subset_image_univ
    [Fintype V] (f : V → W) (c : Chain V) {tau : Finset W}
    (htau : tau ∈ (normalizedMapChainHom f c).support) :
    tau ⊆ (Finset.univ : Finset V).image f := by
  intro w hw
  by_contra hwRange
  rw [Finsupp.mem_support_iff] at htau
  apply htau
  rw [normalizedMapChainHom]
  simp only [Finsupp.liftAddHom_apply, Finsupp.sum_apply]
  calc
    c.sum (fun sigma a =>
        ({ toFun := fun a => a • normalizedMapSimplex f sigma
           map_zero' := zero_smul _ _
           map_add' := fun a b => add_smul a b _ } :
          ZMod 2 →+ Chain W) a tau) =
        c.sum (fun _ _ => (0 : ZMod 2)) := by
      apply Finsupp.sum_congr
      intro sigma hsigma
      by_cases hf : (sigma.image f).card = sigma.card
      · rw [normalizedMapSimplex, if_pos hf]
        have htauNe : tau ≠ sigma.image f := by
          intro h
          apply hwRange
          have hw' : w ∈ sigma.image f := by
            rw [← h]
            exact hw
          exact (Finset.image_mono f (Finset.subset_univ sigma)) hw'
        simp [singletonChain, htauNe]
      · rw [normalizedMapSimplex, if_neg hf]
        simp
    _ = 0 := by simp

private theorem normalizedBoundary_degenerate (f : V → W) (sigma : Finset V)
    (hf : ¬ Set.InjOn f sigma) :
    ∑ v ∈ sigma, normalizedMapSimplex f (sigma.erase v) = 0 := by
  let T := sigma.filter fun v ↦ Set.InjOn f (sigma.erase v)
  by_cases hT : T = ∅
  · apply Finset.sum_eq_zero
    intro v hv
    apply normalizedMapSimplex_eq_zero_of_not_injOn
    intro hinj
    have : v ∈ T := Finset.mem_filter.mpr ⟨hv, hinj⟩
    simp [hT] at this
  · obtain ⟨v, hvT⟩ := Finset.nonempty_iff_ne_empty.mpr hT
    have hvSigma : v ∈ sigma := (Finset.mem_filter.mp hvT).1
    have hinjV : Set.InjOn f (sigma.erase v) := (Finset.mem_filter.mp hvT).2
    have hfvImage : f v ∈ (sigma.erase v).image f := by
      by_contra hnot
      apply hf
      intro a ha b hb hab
      by_cases hav : a = v
      · subst a
        by_cases hbv : b = v
        · exact hbv.symm
        · exact (hnot (Finset.mem_image.mpr
            ⟨b, Finset.mem_erase.mpr ⟨hbv, hb⟩, hab.symm⟩)).elim
      · by_cases hbv : b = v
        · subst b
          exact (hnot (Finset.mem_image.mpr
            ⟨a, Finset.mem_erase.mpr ⟨hav, ha⟩, hab⟩)).elim
        · exact hinjV (Finset.mem_erase.mpr ⟨hav, ha⟩)
            (Finset.mem_erase.mpr ⟨hbv, hb⟩) hab
    obtain ⟨y, hyErase, hyv⟩ := Finset.mem_image.mp hfvImage
    have hySigma : y ∈ sigma := (Finset.mem_erase.mp hyErase).2
    have hyvNe : y ≠ v := (Finset.mem_erase.mp hyErase).1
    have hpair : ∀ ⦃a b : V⦄, a ∈ sigma → b ∈ sigma → f a = f b →
        a = b ∨ (a = v ∧ b = y) ∨ (a = y ∧ b = v) := by
      intro a b ha hb hab
      by_cases hav : a = v
      · subst a
        by_cases hbv : b = v
        · exact Or.inl hbv.symm
        · right
          left
          refine ⟨rfl, ?_⟩
          exact (hinjV hyErase (Finset.mem_erase.mpr ⟨hbv, hb⟩)
            (hyv.trans hab)).symm
      · by_cases hbv : b = v
        · subst b
          right
          right
          refine ⟨?_, rfl⟩
          apply hinjV (Finset.mem_erase.mpr ⟨hav, ha⟩) hyErase
          exact hab.trans hyv.symm
        · left
          exact hinjV (Finset.mem_erase.mpr ⟨hav, ha⟩)
            (Finset.mem_erase.mpr ⟨hbv, hb⟩) hab
    have hinjY : Set.InjOn f (sigma.erase y) := by
      intro a ha b hb hab
      have haSigma := (Finset.mem_erase.mp ha).2
      have hbSigma := (Finset.mem_erase.mp hb).2
      rcases hpair haSigma hbSigma hab with habEq | havby | haybv
      · exact habEq
      · exact ((Finset.mem_erase.mp hb).1 havby.2).elim
      · exact ((Finset.mem_erase.mp ha).1 haybv.1).elim
    have hyT : y ∈ T := Finset.mem_filter.mpr ⟨hySigma, hinjY⟩
    have hOnly : ∀ z ∈ T, z = v ∨ z = y := by
      intro z hzT
      by_cases hzv : z = v
      · exact Or.inl hzv
      · right
        have hzSigma := (Finset.mem_filter.mp hzT).1
        have hinjZ := (Finset.mem_filter.mp hzT).2
        have hfzImage : f z ∈ (sigma.erase z).image f := by
          by_contra hnot
          apply hf
          intro a ha b hb hab
          by_cases haz : a = z
          · subst a
            by_cases hbz : b = z
            · exact hbz.symm
            · exact (hnot (Finset.mem_image.mpr
                ⟨b, Finset.mem_erase.mpr ⟨hbz, hb⟩, hab.symm⟩)).elim
          · by_cases hbz : b = z
            · subst b
              exact (hnot (Finset.mem_image.mpr
                ⟨a, Finset.mem_erase.mpr ⟨haz, ha⟩, hab⟩)).elim
            · exact hinjZ (Finset.mem_erase.mpr ⟨haz, ha⟩)
                (Finset.mem_erase.mpr ⟨hbz, hb⟩) hab
        obtain ⟨w, hwErase, hwz⟩ := Finset.mem_image.mp hfzImage
        have hwSigma := (Finset.mem_erase.mp hwErase).2
        have hwzNe := (Finset.mem_erase.mp hwErase).1
        rcases hpair hwSigma hzSigma hwz with hwzEq | hwvzy | hwyzv
        · exact (hwzNe hwzEq).elim
        · exact hwvzy.2
        · exact (hzv hwyzv.2).elim
    have hTeq : T = {v, y} := by
      ext z
      constructor
      · intro hz
        rcases hOnly z hz with rfl | rfl <;> simp
      · intro hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hvT
        · exact hyT
    have himage : (sigma.erase y).image f = (sigma.erase v).image f := by
      ext z
      constructor
      · intro hz
        obtain ⟨a, haErase, rfl⟩ := Finset.mem_image.mp hz
        by_cases hav : a = v
        · subst a
          exact Finset.mem_image.mpr ⟨y, hyErase, hyv⟩
        · exact Finset.mem_image.mpr ⟨a,
            Finset.mem_erase.mpr ⟨hav, (Finset.mem_erase.mp haErase).2⟩, rfl⟩
      · intro hz
        obtain ⟨a, haErase, rfl⟩ := Finset.mem_image.mp hz
        by_cases hay : a = y
        · subst a
          exact Finset.mem_image.mpr ⟨v,
            Finset.mem_erase.mpr ⟨fun h ↦ hyvNe h.symm, hvSigma⟩, hyv.symm⟩
        · exact Finset.mem_image.mpr ⟨a,
            Finset.mem_erase.mpr ⟨hay, (Finset.mem_erase.mp haErase).2⟩, rfl⟩
    calc
      (∑ z ∈ sigma, normalizedMapSimplex f (sigma.erase z)) =
          ∑ z ∈ T, normalizedMapSimplex f (sigma.erase z) := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro z hzSigma hzNotT
        exact normalizedMapSimplex_eq_zero_of_not_injOn f _
          (fun hinj ↦ hzNotT (Finset.mem_filter.mpr ⟨hzSigma, hinj⟩))
      _ = normalizedMapSimplex f (sigma.erase v) +
          normalizedMapSimplex f (sigma.erase y) := by
        rw [hTeq]
        simp [Ne.symm hyvNe]
      _ = singletonChain ((sigma.erase v).image f) +
          singletonChain ((sigma.erase y).image f) := by
        rw [normalizedMapSimplex_eq_of_injOn f _ hinjV,
          normalizedMapSimplex_eq_of_injOn f _ hinjY]
      _ = 0 := by
        rw [himage]
        ext tau
        exact CharTwo.add_self_eq_zero _

private theorem image_erase_of_injOn (f : V → W) (sigma : Finset V)
    (hf : Set.InjOn f sigma) {v : V} (hv : v ∈ sigma) :
    (sigma.erase v).image f = (sigma.image f).erase (f v) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hxErase, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image.mpr
      ⟨x, (Finset.mem_erase.mp hxErase).2, rfl⟩⟩
    intro hxv
    exact (Finset.mem_erase.mp hxErase).1
      (hf (Finset.mem_erase.mp hxErase).2 hv hxv)
  · intro hy
    obtain ⟨hyne, x, hxSigma, hxy⟩ :=
      (Finset.mem_erase.mp hy).imp_right Finset.mem_image.mp
    have hxv : x ≠ v := by
      intro hxv
      subst x
      exact hyne hxy.symm
    exact Finset.mem_image.mpr
      ⟨x, Finset.mem_erase.mpr ⟨hxv, hxSigma⟩, hxy⟩

/-- The normalized pushforward commutes with the boundary of one simplex.
The degenerate case is the essential part: either every facet is degenerate,
or exactly two nondegenerate facets have the same image and cancel in `F₂`. -/
theorem normalizedMapChainHom_boundarySimplex (f : V → W) (sigma : Finset V) :
    normalizedMapChainHom f (boundarySimplex sigma) =
      boundary (normalizedMapSimplex f sigma) := by
  by_cases hf : Set.InjOn f sigma
  · rw [boundarySimplex]
    simp only [map_sum, normalizedMapChainHom_singleton]
    rw [normalizedMapSimplex_eq_of_injOn f sigma hf,
      boundary_singletonChain, boundarySimplex]
    rw [Finset.sum_image hf]
    apply Finset.sum_congr rfl
    intro v hv
    rw [normalizedMapSimplex_eq_of_injOn]
    · congr 1
      exact image_erase_of_injOn f sigma hf hv
    · exact hf.mono (Finset.erase_subset v sigma)
  · rw [normalizedMapSimplex_eq_zero_of_not_injOn f sigma hf, boundary_zero]
    rw [boundarySimplex]
    simp only [map_sum, normalizedMapChainHom_singleton]
    exact normalizedBoundary_degenerate f sigma hf

/-- The Section 10 identity `φ_*(∂c) = ∂(φ_*c)` for an arbitrary vertex
map, including maps which collapse vertices. -/
theorem normalizedMapChainHom_boundary (f : V → W) (c : Chain V) :
    normalizedMapChainHom f (boundary c) =
      boundary (normalizedMapChainHom f c) := by
  induction c using Finsupp.induction with
  | zero => simp [boundary, normalizedMapChainHom]
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
      change normalizedMapChainHom f
          (boundary (singletonChain sigma + c)) =
        boundary (normalizedMapChainHom f (singletonChain sigma + c))
      simp only [boundary_add, map_add]
      rw [ih, boundary_singletonChain,
        normalizedMapChainHom_boundarySimplex,
        normalizedMapChainHom_singleton]

end SimplexFamily
end BeyondSperner
