import Mathlib
--import LLMlean

section fiberlemma

open Finset


variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

lemma injOn_sdiff (s : Finset α) (f : α → β) (h : s.card = (Finset.image f s).card + 1) : ∃ a b, a ∈ s ∧ b ∈ s ∧ f a = f b ∧ a ≠ b ∧ Set.InjOn f (s \ ({a, b} : Finset α)) := by
  have of_card_domain_eq_card_image_succ  (s : Finset α) (f : α → β) (h : s.card = (Finset.image f s).card + 1) :
  ∃ a b, a ∈ s ∧ b ∈ s ∧ f a = f b ∧ a ≠ b := by
    suffices ¬ Set.InjOn f s by
      contrapose! this
      tauto
    by_contra h1
    linarith [Finset.card_image_of_injOn h1]
  obtain ⟨a, b, as, bs, h1, h2⟩ := of_card_domain_eq_card_image_succ s f h
  have absub : {a, b} ⊆ s :=  Finset.insert_subset as (Finset.singleton_subset_iff.mpr bs)
  use a, b
  repeat apply And.intro;assumption
  rw [←Finset.coe_sdiff]
  apply Finset.injOn_of_card_image_eq
  rw [Finset.card_sdiff_of_subset absub]
  · have : (Finset.image f (s \ {a, b})).card = (Finset.image f s).card - 1 := by
      have aux1 : ∀ c, c ∈ s → c ≠ a → c ≠ b → f c ≠ f a := by
        intro c cs ca cb fcfa
        have cardabc : ({a, b, c} : Finset α).card = 3 := by
          rw [Finset.card_eq_three]
          use a, b, c
          tauto
        have abcss : {a, b, c} ⊆ s := by
          apply Finset.insert_subset as
          apply Finset.insert_subset bs (by simp [cs])
        have : (image f s).card < s.card - 1 :=
          calc
            _ = (image f ((s \ {a, b, c}) ∪ {a, b, c})).card :=
              congrArg _ (congrArg _ (Eq.symm (sdiff_union_of_subset abcss)))
            _ = (image f (s \ {a, b, c}) ∪ image f {a, b, c}).card :=
              congrArg _ (Finset.image_union _ _)
            _ ≤ (image f (s \ {a, b, c})).card + (image f {a, b, c}).card :=
              Finset.card_union_le _ _
            _ = (image f (s \ {a, b, c})).card + 1 := by
              simp [Finset.card_eq_one]
              exact ⟨f a, by simp [←h1, fcfa]⟩
            _ ≤ (s \ {a, b, c}).card + 1 := by
              simp [Finset.card_image_le]
            _ = s.card - 3 + 1 := by
              rw [Finset.card_sdiff_of_subset abcss, cardabc]
            _ < _ := by
              have : 2 < s.card := by
                have := Finset.card_le_card abcss
                omega
              omega
        omega
      have aux2 : Finset.image f (s \ {a, b}) = Finset.image f s \ {f a} := by
        ext x
        constructor <;> intro h1'
        · obtain ⟨c, csdiff, fcx⟩ := Finset.mem_image.1 h1'
          obtain ⟨cs, cneab⟩ := Finset.mem_sdiff.1 csdiff
          simp at cneab
          simp
          exact ⟨⟨c, cs, fcx⟩, by simp [← fcx]; exact aux1 c cs cneab.1 cneab.2⟩
        · simp at h1'
          obtain ⟨c, cs, fcx⟩ := h1'.1
          simp [←fcx]
          use c
          simp [cs]
          by_contra! hf
          by_cases ceqa : c = a
          · rw [ceqa] at fcx; rw [fcx] at h1'; tauto
          · rw [hf ceqa, ←h1] at fcx; rw [fcx] at h1; tauto
      rw [aux2, Finset.card_sdiff_of_subset (by
        simpa using Finset.singleton_subset_iff.mpr (Finset.mem_image.mpr ⟨a, as, rfl⟩)),
        card_singleton]
    rw [this,Finset.card_pair h2, h]
    simp

end fiberlemma


open Classical
open Finset

variable {T : Type*} [Inhabited T]
variable {I : Type*}

class IndexedLOrder (I T :Type*) where
  IST : I → LinearOrder T

instance : FunLike (IndexedLOrder I T) I (LinearOrder T) where
  coe := fun a => a.IST
  coe_injective := fun f g h => by cases f; cases g; congr


variable [IST : IndexedLOrder I T]

set_option quotPrecheck false

local notation  lhs "<[" i "]" rhs => (IST i).lt lhs rhs
local notation  lhs "≤[" i "]" rhs => (IST i).le lhs rhs

namespace IndexedLOrder
variable (σ : Finset T) (C : Finset I)

/- Definition of Dominant -/
def isDominant  :=
  ∀ y, ∃ i ∈ C, ∀ x ∈ σ,  y ≤[i] x

variable {σ C} in
lemma Nonempty_of_Dominant (h : IST.isDominant σ C) : C.Nonempty := by
  obtain ⟨j,hj⟩ := h default
  exact ⟨j, hj.1⟩

/- Lemma 1 -/
omit [Inhabited T] in
lemma Dominant_of_subset (σ τ : Finset T) (C : Finset I) :
  τ ⊆ σ → isDominant σ C  → isDominant τ C := by
    intro h1 h2 y
    obtain ⟨j,hj⟩:= h2 y
    use j,hj.1
    intro x hx
    exact hj.2 x (h1 hx)

omit [Inhabited T] in
lemma Dominant_of_supset (σ : Finset T) (C D: Finset I) :
  C ⊆ D → isDominant σ C  → isDominant σ D := by
    intro h1 h2 y
    obtain ⟨j,hj⟩:= h2 y
    use j,(h1 hj.1)
    intro x hx
    exact hj.2 x hx

abbrev mini {σ : Finset T} (h2 : σ.Nonempty) (i : I) : T := @Finset.min' _ (IST i) _ h2

omit [Inhabited T] in
lemma keylemma_of_dominant {σ : Finset T} {C: Finset I} (h1 : IST.isDominant σ C) (h2: σ.Nonempty): σ  = C.image (mini h2)  :=
  by
    ext a
    constructor
    · intro ha
      rw [mem_image]
      by_contra  hm
      push Not at hm
      obtain ⟨i,hi1,hi2⟩ := h1 a
      replace hm := hm i hi1
      rw [mini] at hm
      have ha1 := @Finset.le_min' _ (IST i) _ h2 a hi2
      have ha2 := @Finset.min'_le _ (IST i) _ _ ha
      apply hm
      refine @eq_of_le_of_ge _ (IST i).toPartialOrder _ _ ha2 ha1
    · suffices h: ∀ x ∈ C, mini h2 x = a → a ∈ σ from
      by simp;exact h
      intro _ _ ha
      simp [mini,<-ha,Finset.min'_mem]

omit [Inhabited T] in
lemma card_le_of_isDominant {σ : Finset T} {C: Finset I} (h1 : IST.isDominant σ C) : σ.card  ≤  C.card  := by
  by_cases h2 : σ.Nonempty
  · rw [keylemma_of_dominant h1 h2]
    apply Finset.card_image_le
  · rw [not_nonempty_iff_eq_empty] at h2
    simp only [h2, card_empty, zero_le]

omit [Inhabited T] in
lemma empty_Dominant (h : D.Nonempty) : IST.isDominant Finset.empty D := by
  intro y
  obtain ⟨j,hj⟩ := h
  use j
  constructor
  · exact hj
  · intro x hx
    contradiction

abbrev isCell  := isDominant σ C

abbrev isRoom :=  isCell σ C ∧ C.card = σ.card

lemma sigma_nonempty_of_room {σ : Finset T} {C : Finset I} (h : isRoom σ C) : σ.Nonempty  := by
  have hC : C.Nonempty := Nonempty_of_Dominant h.1
  have hCpos : 0 < C.card := Finset.card_pos.2 hC
  have h_card : σ.card = C.card := h.2.symm
  have hpos : 0 < σ.card := by rwa [h_card]
  exact Finset.card_pos.1 hpos

abbrev isDoor  :=  isCell σ C ∧ C.card = σ.card + 1


variable [DecidableEq T] [DecidableEq I]

inductive isDoorof (τ : Finset T) (D : Finset I) (σ : Finset T) (C : Finset I) : Prop
  | idoor (h0 : isCell σ C) (h1 : isDoor τ D) (x :T) (h1 : x ∉ τ) (h2 : insert x τ = σ) (h3 : D = C)
  | odoor (h0 : isCell σ C) (h1 : isDoor τ D) (j :I) (h1 : j ∉ C) (h2 : τ = σ) (h3 : D = insert j C)

omit [Inhabited T] in
lemma isCell_of_door (h1 : isDoorof τ D σ C) : IST.isCell τ D := by
  cases h1
  · rename_i h0 _ j h1 h3 h4
    rw [h4]
    exact IST.Dominant_of_subset _ _ C (by simp [<-h3]) h0
  · rename_i h0 _ j h1 h2' h3
    rw [h2', h3]
    exact IST.Dominant_of_supset _ _ _ (Finset.subset_insert j C) h0

variable {σ C} in
omit [Inhabited T] in
lemma isRoom_of_Door (h1 : isDoorof τ D σ C) : IST.isRoom σ C := by
  cases h1
  · rename_i h0 h2 x h3 h4 h5
    constructor
    · exact h0
    · simp only [<-h5, h2.2, <-h4, h3, not_false_eq_true, Finset.card_insert_of_notMem]
  · rename_i h0 h2 x h3 h4 h5
    constructor
    · exact h0
    · have h6 := Finset.card_insert_of_notMem h3
      subst h4
      replace h5 : D.card = (insert x C).card := by rw [h5]
      rw [h6] at h5
      rw [h2.2] at h5
      exact Eq.symm $ (add_left_inj _).1 h5

omit [Inhabited T] in
lemma room_is_not_door (h1 : IST.isRoom σ C) : ∀ τ D,  ¬ (isDoorof σ C τ D) := by
  intro τ D hd
  unfold isRoom at h1
  cases hd with
  | idoor h0 hd  x h2 h3 h4 =>
    unfold isDoor at hd
    obtain ⟨_,hd⟩ := hd
    have cond : #σ = #σ +1 := by rw [h1.2] at hd; assumption
    simp at cond
  | odoor h0 hd j h2 h3 h4 =>
    unfold isDoor at hd
    obtain ⟨_,hd⟩ := hd
    have cond : #σ = #σ +1 := by rw [h1.2] at hd; assumption
    simp at cond

variable (τ D) in
abbrev isOutsideDoor := IST.isDoor τ D ∧ τ = Finset.empty

variable (τ D) in
abbrev isInternalDoor := IST.isDoor τ D ∧ τ.Nonempty

/- Lemma 2-/
omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
lemma outsidedoor_singleton (i : I) : IST.isOutsideDoor Finset.empty {i} := by
  constructor
  · rw [isDoor,isCell,isDominant]
    constructor
    · intro y; use i
      constructor
      · exact Finset.mem_singleton.2 (rfl)
      · intro x hx
        contradiction
    · simp only [Finset.card_singleton]
      rfl
  · rfl


--variable (τ D) in
omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
lemma outsidedoor_is_singleton (h : IST.isOutsideDoor τ  D) :  τ = Finset.empty ∧  ∃ i, D = {i} := by
  obtain ⟨h1, h2⟩ := h
  subst h2
  obtain ⟨_,h3⟩ := h1
  replace h4 : D.card = 1 := by
    simp_all
    rfl
  exact ⟨rfl, Finset.card_eq_one.1 h4⟩



section KeyLemma

-- Definition of the sets M_i used in the proof
def M_set (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty) : Set T :=
  {y : T | ∀ k ∈ D, k ≠ i → mini h_nonempty k <[k] y}

-- Predicate for being the maximal element of M_i with respect to <_i
def is_maximal_in_M_set (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty) (x : T) : Prop :=
  x ∈ M_set τ D i h_nonempty ∧ ∀ y ∈ M_set τ D i h_nonempty, y ≤[i] x

-- The maximal element m_i when M_i is nonempty
noncomputable def m_element [Fintype T] (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty)
    (h : (M_set τ D i h_nonempty).Nonempty) : T :=
  @Finset.max' _ (IST i) (M_set τ D i h_nonempty).toFinset (Set.toFinset_nonempty.mpr h)

-- Theorem: m_element is indeed the maximal element
omit[Inhabited T][DecidableEq T][DecidableEq I] in
theorem m_element_is_maximal [Fintype T] (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty)
    (h : (M_set τ D i h_nonempty).Nonempty) :
    is_maximal_in_M_set τ D i h_nonempty (m_element τ D i h_nonempty h) := by
  unfold is_maximal_in_M_set m_element
  let s_finset := (M_set τ D i h_nonempty).toFinset
  have h_nonempty_finset: s_finset.Nonempty := Set.toFinset_nonempty.mpr h
  constructor
  · rw [←Set.mem_toFinset]
    exact @Finset.max'_mem _ (IST i) s_finset h_nonempty_finset
  · intros y hy
    rw [←Set.mem_toFinset] at hy
    apply @Finset.le_max' _ (IST i)
    exact hy

-- Sublemma 3.1: τ is dominant with respect to D - i iff i ∈ {a,b} and M_i = ∅
omit [Inhabited T] in
lemma isDominant_erase_iff_M_set_empty [Fintype T] (τ : Finset T) (D : Finset I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) :
    ∀ i ∈ D, (IST.isDominant τ (D.erase i) ↔
      (∃ a b, a ∈ D ∧ b ∈ D ∧ a ≠ b ∧
       mini h_nonempty a = mini h_nonempty b ∧
       (i = a ∨ i = b) ∧
       M_set τ D i h_nonempty = ∅)) := by
  intro i hi
  constructor
  · intro h_dom
    have h_card : D.card = τ.card + 1 := h_door.2
    have h_image_card : D.card = (D.image (mini h_nonempty)).card + 1 := by
      have h_dominant : IST.isDominant τ D := h_door.1
      have h_image_sub : D.image (mini h_nonempty) ⊆ τ := by
        intro x hx
        simp at hx
        obtain ⟨j, _, hj_eq⟩ := hx
        rw [←hj_eq, mini]
        exact @Finset.min'_mem _ (IST j) τ h_nonempty
      have h_image_eq : D.image (mini h_nonempty) = τ := by
        convert (keylemma_of_dominant h_dominant h_nonempty).symm
      rw [h_card, h_image_eq]
    obtain ⟨a, b, ha_mem, hb_mem, h_eq_mini, h_ne, _⟩ := injOn_sdiff D (mini h_nonempty) h_image_card
    use a, b, ha_mem, hb_mem, h_ne, h_eq_mini
    by_cases h_case : i = a ∨ i = b
    · constructor
      · exact h_case
      · ext y
        simp [M_set]
        obtain ⟨k, hk_in_erase, hk_dom⟩ := h_dom y
        have hk_in_D : k ∈ D := (Finset.mem_erase.mp hk_in_erase).2
        have hk_ne_i : k ≠ i := (Finset.mem_erase.mp hk_in_erase).1
        use k, hk_in_D, hk_ne_i
    · push Not at h_case
      obtain ⟨h_i_ne_a, h_i_ne_b⟩ := h_case

      have h_a_in_erase : a ∈ D.erase i := Finset.mem_erase.mpr ⟨h_i_ne_a.symm, ha_mem⟩
      have h_b_in_erase : b ∈ D.erase i := Finset.mem_erase.mpr ⟨h_i_ne_b.symm, hb_mem⟩

      have h_not_inj : ¬Set.InjOn (mini h_nonempty) (D.erase i : Set I) := by
        intro h_inj
        exact h_ne (h_inj h_a_in_erase h_b_in_erase h_eq_mini)

      have h_image_lt : ((D.erase i).image (mini h_nonempty)).card < (D.erase i).card := by
        by_contra h_not_lt
        push Not at h_not_lt
        have h_eq : ((D.erase i).image (mini h_nonempty)).card = (D.erase i).card :=
          le_antisymm Finset.card_image_le h_not_lt
        have h_inj : Set.InjOn (mini h_nonempty) (D.erase i : Set I) :=
          Finset.injOn_of_card_image_eq h_eq
        exact h_not_inj h_inj
      exfalso
      have h_dom_image := keylemma_of_dominant h_dom h_nonempty
      have h_tau_eq_image : τ.card = ((D.erase i).image (mini h_nonempty)).card := by
        congr; ext; simp [h_dom_image]
      have h_tau_eq_erase : τ.card = (D.erase i).card := by
        rw [Finset.card_erase_of_mem hi, h_door.2]; simp
      rw [h_tau_eq_erase] at h_tau_eq_image
      rw [h_tau_eq_image] at h_image_lt
      exact not_lt.mpr (le_refl _) h_image_lt
  · rintro ⟨a, b, ha_mem, hb_mem, h_ne, h_eq_mini, h_i_case, h_Mi_empty⟩
    intro y
    unfold M_set at h_Mi_empty
    simp only [Set.mem_ofPred_eq, Set.eq_empty_iff_forall_notMem] at h_Mi_empty
    specialize h_Mi_empty y
    push Not at h_Mi_empty
    obtain ⟨k, hk_mem, hk_ne_i, hk_not_lt⟩ := h_Mi_empty
    use k
    constructor
    · exact Finset.mem_erase.mpr ⟨hk_ne_i, hk_mem⟩
    · intro x hx
      let : LinearOrder T := IST k
      have h_y_le_mini : y ≤[k] mini h_nonempty k := hk_not_lt
      have h_mini_le_x : mini h_nonempty k ≤[k] x := Finset.min'_le τ x hx
      exact @le_trans _ (IST k).toPreorder _ _ _ h_y_le_mini h_mini_le_x

/- Equations (1) and (2) in Sublemma 3.2 of the paper. -/
omit [Inhabited T] [DecidableEq I] in
lemma mini_insert_eq_old_or_new (τ : Finset T) (h_nonempty : τ.Nonempty)
    (x : T) (i : I) :
    mini (Finset.insert_nonempty x τ) i = mini h_nonempty i ∨
      mini (Finset.insert_nonempty x τ) i = x := by
  let := IST i
  change (insert x τ).min' _ = τ.min' h_nonempty ∨ (insert x τ).min' _ = x
  have hmin : (insert x τ).min' (Finset.insert_nonempty x τ) =
      min x (τ.min' h_nonempty) := by
    convert (@Finset.min'_insert T (IST i) x τ h_nonempty) using 1
    apply le_antisymm
    · apply Finset.le_min'
      intro y hy
      apply Finset.min'_le
      simpa using hy
    · apply Finset.le_min'
      intro y hy
      apply Finset.min'_le
      simpa using hy
  rw [hmin]
  rcases le_total x (τ.min' h_nonempty) with h | h
  · exact Or.inr (min_eq_left h)
  · exact Or.inl (min_eq_right h)

-- Sublemma 3.2: inserting x preserves dominance exactly when x is maximal in M_i.
omit [Inhabited T] in
lemma isDominant_insert_iff_maximal_in_M_set [Fintype T]
    (τ : Finset T) (D : Finset I) (x : T)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) (h_not_mem : x ∉ τ)
    (a b : I) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (h_eq : mini h_nonempty a = mini h_nonempty b) :
    IST.isDominant (insert x τ) D ↔
    (∃ i ∈ ({a, b} : Finset I), (M_set τ D i h_nonempty).Nonempty ∧
     is_maximal_in_M_set τ D i h_nonempty x) := by
  constructor
  · intro h_dominant
    have h_insert_nonempty : (insert x τ).Nonempty := Finset.insert_nonempty x τ
    have h_min_eq_image : D.image (mini h_insert_nonempty) = insert x τ := by
      convert (keylemma_of_dominant h_dominant h_insert_nonempty).symm
    have h_x_is_min : ∃ i ∈ D, mini h_insert_nonempty i = x := by
      have h_x_in_image : x ∈ D.image (mini h_insert_nonempty) := by
        rw [h_min_eq_image]
        exact Finset.mem_insert_self x τ
      exact Finset.mem_image.mp h_x_in_image
    obtain ⟨i, hi_mem, hi_eq⟩ := h_x_is_min
    have h_is_room : isRoom (insert x τ) D := by
      unfold isRoom
      constructor
      · exact h_dominant
      · rw [Finset.card_insert_of_notMem h_not_mem, h_door.2]
    have h_inj_insert : Set.InjOn (mini h_insert_nonempty) (D : Set I) := by
      apply Finset.injOn_of_card_image_eq
      rw [h_min_eq_image, h_is_room.2]
    have h_mini_lt_x : ∀ k ∈ D, k ≠ i → mini h_nonempty k <[k] x := by
      intros k hk_mem hk_ne_i
      have h_mini_cases :
          mini h_insert_nonempty k = mini h_nonempty k ∨ mini h_insert_nonempty k = x := by
        simpa only using mini_insert_eq_old_or_new τ h_nonempty x k

      have h_mini_neq_x : mini h_insert_nonempty k ≠ x := by
        intro h_eq
        have h_inj : Set.InjOn (mini h_insert_nonempty) (D : Set I) := h_inj_insert
        have hi_mem_D : i ∈ D := hi_mem
        have hk_mem_D : k ∈ D := hk_mem
        have h_mini_i_eq_x : mini h_insert_nonempty i = x := hi_eq
        exact hk_ne_i (h_inj hi_mem_D hk_mem_D (h_mini_i_eq_x.trans h_eq.symm)).symm
      let := IST k
      have h_mini_eq_k : mini h_insert_nonempty k = mini h_nonempty k := by
        cases h_mini_cases with
        | inl h => exact h
        | inr h => exact absurd h h_mini_neq_x
      apply lt_of_le_of_ne
      · have h_le : mini h_insert_nonempty k ≤[k] x := by
          apply @Finset.min'_le _ (IST k)
          exact Finset.mem_insert_self x τ
        rw [h_mini_eq_k] at h_le
        exact h_le
      · exact fun h_eq_x => h_not_mem (h_eq_x ▸ Finset.min'_mem τ h_nonempty)
    have h_x_le_mini_i : x ≤[i] mini h_nonempty i := by
      let := IST i
      rw [← hi_eq]
      unfold mini
      apply Finset.min'_le
      · exact Finset.mem_insert_of_mem (Finset.min'_mem _ h_nonempty)
    have h_i_in_ab : i ∈ ({a, b} : Finset I) := by
      by_cases hik : i = a ∨ i = b
      · simp [hik]
      · push Not at hik
        obtain ⟨hia, hib⟩ := hik
        have h_mini_eq_for_ne_i : ∀ k ∈ D, k ≠ i → mini h_insert_nonempty k = mini h_nonempty k := by
          intros k hk_mem hk_ne_i
          have h_cases :
              mini h_insert_nonempty k = mini h_nonempty k ∨ mini h_insert_nonempty k = x := by
            simpa only using mini_insert_eq_old_or_new τ h_nonempty x k

          have h_mini_neq_x : mini h_insert_nonempty k ≠ x := by
            intro h_eq_k_x
            exact hk_ne_i (h_inj_insert hk_mem hi_mem (h_eq_k_x.trans hi_eq.symm))
          cases h_cases with
          | inl h => exact h
          | inr h => exact absurd h h_mini_neq_x
        have h_mini_a_eq : mini h_insert_nonempty a = mini h_nonempty a := h_mini_eq_for_ne_i a ha (Ne.symm hia)
        have h_mini_b_eq : mini h_insert_nonempty b = mini h_nonempty b := h_mini_eq_for_ne_i b hb (Ne.symm hib)
        have h_contr : mini h_insert_nonempty a = mini h_insert_nonempty b := by
          rw [h_mini_a_eq, h_mini_b_eq, h_eq]
        exact (hab (h_inj_insert ha hb h_contr)).elim
    use i, h_i_in_ab
    constructor
    · have h_nonempty_M : (M_set τ D i h_nonempty).Nonempty := by
        use x
        unfold M_set
        apply Set.mem_ofPred.mpr
        intro k hk_mem hk_ne_i
        exact h_mini_lt_x k hk_mem hk_ne_i
      exact h_nonempty_M
    · unfold is_maximal_in_M_set
      constructor
      · unfold M_set
        apply Set.mem_ofPred.mpr
        intro k hk_mem hk_ne_i
        exact h_mini_lt_x k hk_mem hk_ne_i
      · intros y hy
        let := IST i
        unfold M_set at hy
        simp at hy
        obtain ⟨k, hk_in_D, h_y_le_all⟩ := h_dominant y
        by_cases hik : k = i
        · subst hik
          exact h_y_le_all x (Finset.mem_insert_self x τ)
        · have h_lt_y : mini h_nonempty k <[k] y := hy k hk_in_D hik
          have h_mini_mem : mini h_nonempty k ∈ τ := by
            unfold mini
            exact @Finset.min'_mem _ (IST k) _ h_nonempty
          have h_mini_mem_insert : mini h_nonempty k ∈ insert x τ := Finset.mem_insert_of_mem h_mini_mem
          have h_le_m : y ≤[k] mini h_nonempty k := h_y_le_all (mini h_nonempty k) h_mini_mem_insert
          let := IST k
          exact absurd (lt_of_lt_of_le h_lt_y h_le_m) (lt_irrefl _)

  · rintro ⟨i, hi_mem_ab, h_M_nonempty, h_x_is_max⟩
    have h_x_in_M : x ∈ M_set τ D i h_nonempty := h_x_is_max.1
    unfold isDominant
    intro y
    have h_dom_tau := h_door.1
    obtain ⟨k, hk_in_D, hk_dom⟩ := h_dom_tau y
    by_cases h_k_eq_i : k = i
    · subst h_k_eq_i
      have hk_in_D : k ∈ D := by
        cases Finset.mem_insert.mp hi_mem_ab with
        | inl hk_eq_a => rwa [hk_eq_a]
        | inr hk_eq_b => have : k = b := Finset.mem_singleton.mp hk_eq_b; rw [this]; exact hb
      let := IST k
      by_cases h_y_le_x : y ≤[k] x
      · use k, hk_in_D
        intro z hz
        cases Finset.mem_insert.mp hz with
        | inl h_z_eq_x => rw [h_z_eq_x]; exact h_y_le_x
        | inr h_z_in_tau => exact hk_dom z h_z_in_tau
      · have h_x_lt_y : x <[k] y := lt_of_not_ge h_y_le_x
        have h_y_not_in_M : y ∉ M_set τ D k h_nonempty := by
          intro h_y_in_M
          have h_y_le_x : y ≤[k] x := h_x_is_max.2 y h_y_in_M
          exact not_le.mpr h_x_lt_y h_y_le_x
        simp [M_set] at h_y_not_in_M
        push Not at h_y_not_in_M
        obtain ⟨j, hj_in_D, hj_ne_k, hj_not_lt⟩ := h_y_not_in_M
        use j, hj_in_D
        intro z hz
        cases Finset.mem_insert.mp hz with
        | inl h_z_eq_x =>
          rw [h_z_eq_x]
          let := IST j
          have h_mini_lt_x : mini h_nonempty j <[j] x := h_x_in_M j hj_in_D hj_ne_k
          have h_y_le_mini : y ≤[j] mini h_nonempty j := le_of_not_gt hj_not_lt
          exact le_of_lt (lt_of_le_of_lt h_y_le_mini h_mini_lt_x)
        | inr h_z_in_tau =>
          let := IST j
          have h_y_le_mini : y ≤[j] mini h_nonempty j := le_of_not_gt hj_not_lt
          have h_mini_le_z : mini h_nonempty j ≤[j] z := Finset.min'_le τ z h_z_in_tau
          exact le_trans h_y_le_mini h_mini_le_z
    · use k, hk_in_D
      intro z hz
      cases Finset.mem_insert.mp hz with
      | inl h_z_eq_x =>
        rw [h_z_eq_x]
        let := IST k
        have h_y_le_mini : y ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (Finset.min'_mem τ h_nonempty)
        have h_mini_lt_x : mini h_nonempty k <[k] x := h_x_in_M k hk_in_D h_k_eq_i
        exact le_of_lt (lt_of_le_of_lt h_y_le_mini h_mini_lt_x)
      | inr h_z_in_tau =>
        exact hk_dom z h_z_in_tau


-- Key lemma: M_a and M_b are disjoint
omit [Inhabited T][DecidableEq T] in
lemma M_sets_disjoint [Fintype T] (τ : Finset T) (D : Finset I) (a b : I)
    (h_nonempty : τ.Nonempty) (h_door : IST.isDoor τ D)
    (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (h_eq : mini h_nonempty a = mini h_nonempty b) :
    M_set τ D a h_nonempty ∩ M_set τ D b h_nonempty = ∅ := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false]
  constructor
  · intro ⟨h_in_a, h_in_b⟩
    unfold M_set at h_in_a h_in_b
    have h_b_ne_a : b ≠ a := hab.symm
    have h_mini_b_lt_y : mini h_nonempty b <[b] y := h_in_a b hb h_b_ne_a
    have h_mini_a_lt_y : mini h_nonempty a <[a] y := h_in_b a ha hab
    rw [h_eq] at h_mini_a_lt_y
    obtain ⟨k, hk_in_D, hk_dom⟩ := h_door.1 y
    have h_mini_b_mem : mini h_nonempty b ∈ τ := by
      unfold mini
      exact @Finset.min'_mem _ (IST b) _ h_nonempty
    have h_y_le_mini_b : y ≤[k] mini h_nonempty b := hk_dom (mini h_nonempty b) h_mini_b_mem
    by_cases hk_eq_a : k = a
    · subst hk_eq_a
      let := IST k
      exact not_le.mpr h_mini_a_lt_y h_y_le_mini_b
    · by_cases hk_eq_b : k = b
      · subst hk_eq_b
        let := IST k
        exact not_le.mpr h_mini_b_lt_y h_y_le_mini_b
      · have h_mini_k_lt_y : mini h_nonempty k <[k] y := h_in_a k hk_in_D hk_eq_a
        have h_mini_k_mem : mini h_nonempty k ∈ τ := by
          unfold mini
          exact @Finset.min'_mem _ (IST k) _ h_nonempty
        have h_y_le_mini_k : y ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) h_mini_k_mem
        let := IST k
        exact not_le.mpr h_mini_k_lt_y h_y_le_mini_k
  · intro h
    exact False.elim h

omit [Inhabited T][DecidableEq T] in
lemma m_element_not_in_tau [Fintype T] (τ : Finset T) (D : Finset I) (i a b : I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (h_M_nonempty : (M_set τ D i h_nonempty).Nonempty)
    (h_i_is : i = a ∨ i = b) :
    m_element τ D i h_nonempty h_M_nonempty ∉ τ := by
  let m_i := m_element τ D i h_nonempty h_M_nonempty
  have h_max : is_maximal_in_M_set τ D i h_nonempty m_i :=
    m_element_is_maximal τ D i h_nonempty h_M_nonempty
  intro h_m_in_tau
  obtain ⟨k, hk_mem, hk_dom⟩ := h_door.1 m_i
  by_cases hk_eq_i : k = i
  · subst hk_eq_i
    have h_m_le_mini : m_i ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (by
      unfold mini
      exact @Finset.min'_mem _ (IST k) _ h_nonempty)
    have h_m_eq_mini : m_i = mini h_nonempty k := by
      let := IST k
      have h_mini_le_m : mini h_nonempty k ≤[k] m_i := Finset.min'_le τ m_i h_m_in_tau
      exact le_antisymm h_m_le_mini h_mini_le_m
    have h_m_in_M : m_i ∈ M_set τ D k h_nonempty := h_max.1
    unfold M_set at h_m_in_M
    cases h_i_is with
    | inl hi_eq_a =>
      subst hi_eq_a
      have h_mini_b_lt_m : mini h_nonempty b <[b] m_i := h_m_in_M b hb_mem hab.symm
      rw [h_m_eq_mini, h_eq_mini] at h_mini_b_lt_m
      let := IST b
      exact lt_irrefl (mini h_nonempty b) h_mini_b_lt_m
    | inr hi_eq_b =>
      subst hi_eq_b
      have h_mini_a_lt_m : mini h_nonempty a <[a] m_i := h_m_in_M a ha_mem hab
      rw [h_m_eq_mini, ← h_eq_mini] at h_mini_a_lt_m
      let := IST a
      exact lt_irrefl (mini h_nonempty a) h_mini_a_lt_m
  · have h_m_in_M : m_i ∈ M_set τ D i h_nonempty := h_max.1
    unfold M_set at h_m_in_M
    have h_mini_k_lt_m : mini h_nonempty k <[k] m_i := h_m_in_M k hk_mem hk_eq_i
    have h_m_le_mini_k : m_i ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (by
      unfold mini
      exact @Finset.min'_mem _ (IST k) _ h_nonempty)
    let := IST k
    exact not_le.mpr h_mini_k_lt_m h_m_le_mini_k

omit [Inhabited T] in
lemma odoor_index_in_pair [Fintype T] (τ : Finset T) (D : Finset I) (C : Finset I)
    (a b j : I) (_h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (h_dom : IST.isDominant τ C) (h_room_card : C.card = τ.card)
    (_hj_not_mem : j ∉ C) (hc_eq : D = insert j C) :
    j ∈ ({a, b} : Finset I) := by
  by_contra h_not_in
  simp only [Finset.mem_insert, Finset.mem_singleton] at h_not_in
  push Not at h_not_in
  obtain ⟨hj_ne_a, hj_ne_b⟩ := h_not_in
  have ha_in_C : a ∈ C := by
    have ha_in_D : a ∈ D := ha_mem
    rw [hc_eq] at ha_in_D
    cases Finset.mem_insert.mp ha_in_D with
    | inl h_eq => exact absurd h_eq (Ne.symm hj_ne_a)
    | inr h_mem => exact h_mem
  have hb_in_C : b ∈ C := by
    have hb_in_D : b ∈ D := hb_mem
    rw [hc_eq] at hb_in_D
    cases Finset.mem_insert.mp hb_in_D with
    | inl h_eq => exact absurd h_eq (Ne.symm hj_ne_b)
    | inr h_mem => exact h_mem
  have h_inj_C : Set.InjOn (mini h_nonempty) (C : Set I) := by
    apply Finset.injOn_of_card_image_eq
    have h_tau_eq_C_image : τ = C.image (mini h_nonempty) := by
      convert keylemma_of_dominant h_dom h_nonempty
    rw [←h_tau_eq_C_image]
    exact h_room_card.symm
  exact hab (h_inj_C ha_in_C hb_in_C h_eq_mini)

omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
lemma maximal_element_unique [Fintype T] (τ : Finset T) (D : Finset I) (i : I)
    (h_nonempty : τ.Nonempty) (h_M_nonempty : (M_set τ D i h_nonempty).Nonempty)
    (x : T) (h_x_max : is_maximal_in_M_set τ D i h_nonempty x) :
    x = m_element τ D i h_nonempty h_M_nonempty := by
  let m_i := m_element τ D i h_nonempty h_M_nonempty
  have h_mi_max : is_maximal_in_M_set τ D i h_nonempty m_i :=
    m_element_is_maximal τ D i h_nonempty h_M_nonempty
  let := IST i
  have h_x_in_M : x ∈ M_set τ D i h_nonempty := h_x_max.1
  have h_mi_in_M : m_i ∈ M_set τ D i h_nonempty := h_mi_max.1
  have h_x_le_mi : x ≤[i] m_i := h_mi_max.2 x h_x_in_M
  have h_mi_le_x : m_i ≤[i] x := h_x_max.2 m_i h_mi_in_M
  exact le_antisymm h_x_le_mi h_mi_le_x

omit [Inhabited T] in
lemma idoor_determines_element [Fintype T] (τ : Finset T) (D : Finset I)
    (a b : I) (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (h_Ma_nonempty : (M_set τ D a h_nonempty).Nonempty)
    (h_Mb_nonempty : (M_set τ D b h_nonempty).Nonempty)
    (x : T) (h_room : IST.isRoom (insert x τ) D)
    (hx_not_mem : x ∉ τ) :
    x = m_element τ D a h_nonempty h_Ma_nonempty ∨
    x = m_element τ D b h_nonempty h_Mb_nonempty := by
  have h_dom : IST.isDominant (insert x τ) D := h_room.1
  have h_exists_max : ∃ i ∈ ({a, b} : Finset I), (M_set τ D i h_nonempty).Nonempty ∧
      is_maximal_in_M_set τ D i h_nonempty x := by
    apply (isDominant_insert_iff_maximal_in_M_set τ D x h_door h_nonempty hx_not_mem
      a b ha_mem hb_mem hab h_eq_mini).mp
    exact h_dom
  obtain ⟨i, hi_mem, hi_nonempty, hi_max⟩ := h_exists_max
  have h_x_eq_mi : x = m_element τ D i h_nonempty hi_nonempty :=
    maximal_element_unique τ D i h_nonempty hi_nonempty x hi_max
  cases Finset.mem_insert.mp hi_mem with
  | inl hi_eq_a =>
    left
    subst hi_eq_a
    exact h_x_eq_mi
  | inr hi_eq_b =>
    right
    have heq : i = b := Finset.mem_singleton.mp hi_eq_b
    subst heq
    exact h_x_eq_mi

/- The two constructions used in Lemma 3 of Ivanov's paper.  Keeping them as
ordinary lemmas makes the four empty/nonempty cases in the incidence proof
read exactly like the paper, without changing the room/door definitions. -/
omit [Inhabited T] in
lemma room_and_door_of_M_nonempty [Fintype T]
    (τ : Finset T) (D : Finset I) (a b i : I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (hi : i = a ∨ i = b) (hMi : (M_set τ D i h_nonempty).Nonempty) :
    IST.isRoom (insert (m_element τ D i h_nonempty hMi) τ) D ∧
      isDoorof τ D (insert (m_element τ D i h_nonempty hMi) τ) D := by
  have hmi_not_mem : m_element τ D i h_nonempty hMi ∉ τ :=
    m_element_not_in_tau τ D i a b h_door h_nonempty ha_mem hb_mem hab
      h_eq_mini hMi hi
  have hi_pair : i ∈ ({a, b} : Finset I) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
  have hdom :
      IST.isDominant (insert (m_element τ D i h_nonempty hMi) τ) D :=
    (isDominant_insert_iff_maximal_in_M_set τ D (m_element τ D i h_nonempty hMi)
      h_door h_nonempty
      hmi_not_mem a b ha_mem hb_mem hab h_eq_mini).2
      ⟨i, hi_pair, hMi, m_element_is_maximal τ D i h_nonempty hMi⟩
  have hroom : IST.isRoom (insert (m_element τ D i h_nonempty hMi) τ) D := by
    refine ⟨hdom, ?_⟩
    rw [Finset.card_insert_of_notMem hmi_not_mem, h_door.2]
  exact ⟨hroom, isDoorof.idoor hdom h_door _ hmi_not_mem rfl rfl⟩

omit [Inhabited T] in
lemma room_and_door_of_M_empty [Fintype T]
    (τ : Finset T) (D : Finset I) (a b i : I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (hi_mem : i ∈ D) (hi : i = a ∨ i = b)
    (hMi : M_set τ D i h_nonempty = ∅) :
    IST.isRoom τ (D.erase i) ∧ isDoorof τ D τ (D.erase i) := by
  have hdom : IST.isDominant τ (D.erase i) :=
    (isDominant_erase_iff_M_set_empty τ D h_door h_nonempty i hi_mem).2
      ⟨a, b, ha_mem, hb_mem, hab, h_eq_mini, hi, hMi⟩
  have hroom : IST.isRoom τ (D.erase i) := by
    refine ⟨hdom, ?_⟩
    rw [Finset.card_erase_of_mem hi_mem, h_door.2]
    omega
  exact ⟨hroom, isDoorof.odoor hdom h_door i (Finset.notMem_erase i D) rfl
    (Finset.insert_erase hi_mem).symm⟩

omit [Inhabited T] in
lemma incident_room_classification [Fintype T]
    (τ : Finset T) (D : Finset I) (a b : I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (σ : Finset T) (C : Finset I) (h_room : IST.isRoom σ C)
    (h_door_rel : isDoorof τ D σ C) :
    (∃ x i, x ∉ τ ∧ i ∈ ({a, b} : Finset I) ∧
      (M_set τ D i h_nonempty).Nonempty ∧
      is_maximal_in_M_set τ D i h_nonempty x ∧
      σ = insert x τ ∧ C = D) ∨
    (∃ i, i ∈ ({a, b} : Finset I) ∧ M_set τ D i h_nonempty = ∅ ∧
      σ = τ ∧ C = D.erase i) := by
  cases h_door_rel with
  | idoor hdom _ x hx_not_mem h_insert h_colors =>
      have hdom' : IST.isDominant (insert x τ) D := by
        simpa only [h_insert, h_colors] using hdom
      obtain ⟨i, hi_pair, hMi, hmax⟩ :=
        (isDominant_insert_iff_maximal_in_M_set τ D x h_door h_nonempty hx_not_mem
          a b ha_mem hb_mem hab
          h_eq_mini).1 hdom'
      exact Or.inl ⟨x, i, hx_not_mem, hi_pair, hMi, hmax, h_insert.symm, h_colors.symm⟩
  | odoor hdom _ i hi_not_mem h_tau h_insert =>
      have hdom' : IST.isDominant τ C := by
        simpa only [h_tau] using hdom
      have hcard : C.card = τ.card := by
        simpa only [h_tau] using h_room.2
      have hi_mem : i ∈ D := by
        rw [h_insert]
        exact Finset.mem_insert_self i C
      have hi_pair : i ∈ ({a, b} : Finset I) :=
        odoor_index_in_pair τ D C a b i h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini hdom' hcard hi_not_mem h_insert
      have hC : C = D.erase i := by
        rw [h_insert]
        exact (Finset.erase_insert hi_not_mem).symm
      have hdom_erase : IST.isDominant τ (D.erase i) := by
        simpa only [← hC] using hdom'
      obtain ⟨_, _, _, _, _, _, _, hMi⟩ :=
        (isDominant_erase_iff_M_set_empty τ D h_door h_nonempty i hi_mem).1 hdom_erase
      exact Or.inr ⟨i, hi_pair, hMi, h_tau.symm, hC⟩

omit [Inhabited T] in
lemma incident_room_eq_of_both_M_nonempty [Fintype T]
    (τ : Finset T) (D : Finset I) (a b : I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (hMa : (M_set τ D a h_nonempty).Nonempty)
    (hMb : (M_set τ D b h_nonempty).Nonempty)
    (σ : Finset T) (C : Finset I) (h_room : IST.isRoom σ C)
    (h_door_rel : isDoorof τ D σ C) :
    (σ = insert (m_element τ D a h_nonempty hMa) τ ∧ C = D) ∨
      (σ = insert (m_element τ D b h_nonempty hMb) τ ∧ C = D) := by
  rcases incident_room_classification τ D a b h_door h_nonempty ha_mem hb_mem hab
      h_eq_mini σ C h_room h_door_rel with hInner | hOuter
  · obtain ⟨x, i, _, hi, _, hmax, hσ, hC⟩ := hInner
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      left
      exact ⟨by simpa only [maximal_element_unique τ D a h_nonempty hMa x hmax] using hσ, hC⟩
    · have hi : i = b := Finset.mem_singleton.mp hi
      subst i
      right
      exact ⟨by simpa only [maximal_element_unique τ D b h_nonempty hMb x hmax] using hσ, hC⟩
  · obtain ⟨i, hi, hMi, _, _⟩ := hOuter
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      exact ((Set.not_nonempty_iff_eq_empty.mpr hMi) hMa).elim
    · have hi : i = b := Finset.mem_singleton.mp hi
      subst i
      exact ((Set.not_nonempty_iff_eq_empty.mpr hMi) hMb).elim

omit [Inhabited T] in
lemma incident_room_eq_of_left_M_nonempty [Fintype T]
    (τ : Finset T) (D : Finset I) (a b : I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (hMa : (M_set τ D a h_nonempty).Nonempty)
    (hMb : M_set τ D b h_nonempty = ∅)
    (σ : Finset T) (C : Finset I) (h_room : IST.isRoom σ C)
    (h_door_rel : isDoorof τ D σ C) :
    (σ = insert (m_element τ D a h_nonempty hMa) τ ∧ C = D) ∨
      (σ = τ ∧ C = D.erase b) := by
  rcases incident_room_classification τ D a b h_door h_nonempty ha_mem hb_mem hab
      h_eq_mini σ C h_room h_door_rel with hInner | hOuter
  · obtain ⟨x, i, _, hi, hMi, hmax, hσ, hC⟩ := hInner
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      left
      exact ⟨by simpa only [maximal_element_unique τ D a h_nonempty hMa x hmax] using hσ, hC⟩
    · have hi : i = b := Finset.mem_singleton.mp hi
      subst i
      exact ((Set.not_nonempty_iff_eq_empty.mpr hMb) hMi).elim
  · obtain ⟨i, hi, hMi, hσ, hC⟩ := hOuter
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      exact ((Set.not_nonempty_iff_eq_empty.mpr hMi) hMa).elim
    · have hi : i = b := Finset.mem_singleton.mp hi
      subst i
      exact Or.inr ⟨hσ, hC⟩

omit [Inhabited T] in
lemma incident_room_eq_of_right_M_nonempty [Fintype T]
    (τ : Finset T) (D : Finset I) (a b : I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (hMa : M_set τ D a h_nonempty = ∅)
    (hMb : (M_set τ D b h_nonempty).Nonempty)
    (σ : Finset T) (C : Finset I) (h_room : IST.isRoom σ C)
    (h_door_rel : isDoorof τ D σ C) :
    (σ = insert (m_element τ D b h_nonempty hMb) τ ∧ C = D) ∨
      (σ = τ ∧ C = D.erase a) := by
  rcases incident_room_classification τ D a b h_door h_nonempty ha_mem hb_mem hab
      h_eq_mini σ C h_room h_door_rel with hInner | hOuter
  · obtain ⟨x, i, _, hi, hMi, hmax, hσ, hC⟩ := hInner
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      exact ((Set.not_nonempty_iff_eq_empty.mpr hMa) hMi).elim
    · have hi : i = b := Finset.mem_singleton.mp hi
      subst i
      left
      exact ⟨by simpa only [maximal_element_unique τ D b h_nonempty hMb x hmax] using hσ, hC⟩
  · obtain ⟨i, hi, hMi, hσ, hC⟩ := hOuter
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      exact Or.inr ⟨hσ, hC⟩
    · have hi : i = b := Finset.mem_singleton.mp hi
      subst i
      exact ((Set.not_nonempty_iff_eq_empty.mpr hMi) hMb).elim

omit [Inhabited T] in
lemma incident_room_eq_of_both_M_empty [Fintype T]
    (τ : Finset T) (D : Finset I) (a b : I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (hMa : M_set τ D a h_nonempty = ∅)
    (hMb : M_set τ D b h_nonempty = ∅)
    (σ : Finset T) (C : Finset I) (h_room : IST.isRoom σ C)
    (h_door_rel : isDoorof τ D σ C) :
    (σ = τ ∧ C = D.erase a) ∨ (σ = τ ∧ C = D.erase b) := by
  rcases incident_room_classification τ D a b h_door h_nonempty ha_mem hb_mem hab
      h_eq_mini σ C h_room h_door_rel with hInner | hOuter
  · obtain ⟨_, i, _, hi, hMi, _, _, _⟩ := hInner
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      exact ((Set.not_nonempty_iff_eq_empty.mpr hMa) hMi).elim
    · have hi : i = b := Finset.mem_singleton.mp hi
      subst i
      exact ((Set.not_nonempty_iff_eq_empty.mpr hMb) hMi).elim
  · obtain ⟨i, hi, _, hσ, hC⟩ := hOuter
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst i
      exact Or.inl ⟨hσ, hC⟩
    · have hi : i = b := Finset.mem_singleton.mp hi
      subst i
      exact Or.inr ⟨hσ, hC⟩

/- Lemma 3-/
omit [Inhabited T] in
theorem internal_door_two_rooms [Fintype T] (τ : Finset T) (D : Finset I)
    (h_int_door : IST.isInternalDoor τ D) :
    ∃ (σ₁ σ₂ : Finset T) (C₁ C₂ : Finset I),
      (σ₁, C₁) ≠ (σ₂, C₂) ∧
      IST.isRoom σ₁ C₁ ∧
      IST.isRoom σ₂ C₂ ∧
      isDoorof τ D σ₁ C₁ ∧
      isDoorof τ D σ₂ C₂ ∧
      (∀ σ C, IST.isRoom σ C → isDoorof τ D σ C →
       (σ = σ₁ ∧ C = C₁) ∨ (σ = σ₂ ∧ C = C₂)) := by
  obtain ⟨h_door, h_nonempty⟩ := h_int_door
  have h_card : D.card = τ.card + 1 := h_door.2
  have h_image_card : D.card = (D.image (mini h_nonempty)).card + 1 := by
    have h_dominant : IST.isDominant τ D := h_door.1
    have h_image_eq : D.image (mini h_nonempty) = τ := by
      convert (keylemma_of_dominant h_dominant h_nonempty).symm
    rw [h_card, h_image_eq]
  obtain ⟨a, b, ha_mem, hb_mem, h_eq_mini, hab, _⟩ := injOn_sdiff D (mini h_nonempty) h_image_card
  have h_disjoint : M_set τ D a h_nonempty ∩ M_set τ D b h_nonempty = ∅ :=
    M_sets_disjoint τ D a b h_nonempty h_door ha_mem hb_mem hab h_eq_mini
  by_cases h_Ma_nonempty : (M_set τ D a h_nonempty).Nonempty
  · by_cases h_Mb_nonempty : (M_set τ D b h_nonempty).Nonempty
    · let m_a := m_element τ D a h_nonempty h_Ma_nonempty
      let m_b := m_element τ D b h_nonempty h_Mb_nonempty
      have h_ma_max : is_maximal_in_M_set τ D a h_nonempty m_a :=
        m_element_is_maximal τ D a h_nonempty h_Ma_nonempty
      have h_mb_max : is_maximal_in_M_set τ D b h_nonempty m_b :=
        m_element_is_maximal τ D b h_nonempty h_Mb_nonempty
      have h_ma_ne_mb : m_a ≠ m_b := by
        intro h_eq
        have h_ma_in_Ma : m_a ∈ M_set τ D a h_nonempty := h_ma_max.1
        have h_mb_in_Mb : m_b ∈ M_set τ D b h_nonempty := h_mb_max.1
        rw [h_eq] at h_ma_in_Ma
        have h_in_inter : m_b ∈ M_set τ D a h_nonempty ∩ M_set τ D b h_nonempty :=
          ⟨h_ma_in_Ma, h_mb_in_Mb⟩
        rw [h_disjoint] at h_in_inter
        exact Set.notMem_empty m_b h_in_inter
      have h_ma_not_mem : m_a ∉ τ :=
        m_element_not_in_tau τ D a a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_Ma_nonempty (Or.inl rfl)
      have h_mb_not_mem : m_b ∉ τ :=
        m_element_not_in_tau τ D b a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_Mb_nonempty (Or.inr rfl)
      obtain ⟨h_room_a, h_door_a⟩ :=
        room_and_door_of_M_nonempty τ D a b a h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini (Or.inl rfl) h_Ma_nonempty
      obtain ⟨h_room_b, h_door_b⟩ :=
        room_and_door_of_M_nonempty τ D a b b h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini (Or.inr rfl) h_Mb_nonempty
      use insert m_a τ, insert m_b τ, D, D
      constructor
      · intro h_pair_eq
        have h_eq : insert m_a τ = insert m_b τ := congr_arg Prod.fst h_pair_eq
        have : m_a = m_b := by
          have h_ma_in : m_a ∈ insert m_a τ := Finset.mem_insert_self m_a τ
          rw [h_eq] at h_ma_in
          cases Finset.mem_insert.mp h_ma_in with
          | inl h => exact h
          | inr h => exact absurd h h_ma_not_mem
        exact h_ma_ne_mb this
      constructor
      · exact h_room_a
      constructor
      · exact h_room_b
      constructor
      · exact h_door_a
      constructor
      · exact h_door_b
      · intros σ C h_room h_door_rel
        simpa only [m_a, m_b] using
          incident_room_eq_of_both_M_nonempty τ D a b h_door h_nonempty ha_mem hb_mem
            hab h_eq_mini h_Ma_nonempty h_Mb_nonempty σ C h_room h_door_rel

    · let m_a := m_element τ D a h_nonempty h_Ma_nonempty
      have h_ma_max : is_maximal_in_M_set τ D a h_nonempty m_a :=
        m_element_is_maximal τ D a h_nonempty h_Ma_nonempty
      have h_ma_not_mem : m_a ∉ τ :=
        m_element_not_in_tau τ D a a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_Ma_nonempty (Or.inl rfl)
      have h_Mb_empty : M_set τ D b h_nonempty = ∅ := Set.not_nonempty_iff_eq_empty.mp h_Mb_nonempty
      obtain ⟨h_room_a, h_door_a⟩ :=
        room_and_door_of_M_nonempty τ D a b a h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini (Or.inl rfl) h_Ma_nonempty
      obtain ⟨h_room_b, h_door_b⟩ :=
        room_and_door_of_M_empty τ D a b b h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini hb_mem (Or.inr rfl) h_Mb_empty
      use insert m_a τ, τ, D, D.erase b
      constructor
      · intro h_pair_eq
        have h_eq : insert m_a τ = τ := congr_arg Prod.fst h_pair_eq
        have h_ma_in : m_a ∈ insert m_a τ := Finset.mem_insert_self m_a τ
        rw [h_eq] at h_ma_in
        exact h_ma_not_mem h_ma_in
      constructor
      · exact h_room_a
      constructor
      · exact h_room_b
      constructor
      · exact h_door_a
      constructor
      · exact h_door_b
      · intros σ C h_room h_door_rel
        simpa only [m_a] using
          incident_room_eq_of_left_M_nonempty τ D a b h_door h_nonempty ha_mem hb_mem
            hab h_eq_mini h_Ma_nonempty h_Mb_empty σ C h_room h_door_rel

  · have h_Ma_empty : M_set τ D a h_nonempty = ∅ := Set.not_nonempty_iff_eq_empty.mp h_Ma_nonempty
    by_cases h_Mb_nonempty : (M_set τ D b h_nonempty).Nonempty
    · let m_b := m_element τ D b h_nonempty h_Mb_nonempty
      have h_mb_max : is_maximal_in_M_set τ D b h_nonempty m_b :=
        m_element_is_maximal τ D b h_nonempty h_Mb_nonempty
      have h_mb_not_mem : m_b ∉ τ :=
        m_element_not_in_tau τ D b a b h_door h_nonempty ha_mem hb_mem hab h_eq_mini h_Mb_nonempty (Or.inr rfl)
      obtain ⟨h_room_b, h_door_b⟩ :=
        room_and_door_of_M_nonempty τ D a b b h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini (Or.inr rfl) h_Mb_nonempty
      obtain ⟨h_room_a, h_door_a⟩ :=
        room_and_door_of_M_empty τ D a b a h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini ha_mem (Or.inl rfl) h_Ma_empty
      use insert m_b τ, τ, D, D.erase a
      constructor
      · intro h_pair_eq
        have h_eq : insert m_b τ = τ := congr_arg Prod.fst h_pair_eq
        have h_mb_in : m_b ∈ insert m_b τ := Finset.mem_insert_self m_b τ
        rw [h_eq] at h_mb_in
        exact h_mb_not_mem h_mb_in
      constructor
      · exact h_room_b
      constructor
      · exact h_room_a
      constructor
      · exact h_door_b
      constructor
      · exact h_door_a
      · intros σ C h_room h_door_rel
        simpa only [m_b] using
          incident_room_eq_of_right_M_nonempty τ D a b h_door h_nonempty ha_mem hb_mem
            hab h_eq_mini h_Ma_empty h_Mb_nonempty σ C h_room h_door_rel

    · have h_Mb_empty : M_set τ D b h_nonempty = ∅ := Set.not_nonempty_iff_eq_empty.mp h_Mb_nonempty
      obtain ⟨h_room_b, h_door_b⟩ :=
        room_and_door_of_M_empty τ D a b b h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini hb_mem (Or.inr rfl) h_Mb_empty
      obtain ⟨h_room_a, h_door_a⟩ :=
        room_and_door_of_M_empty τ D a b a h_door h_nonempty ha_mem hb_mem hab
          h_eq_mini ha_mem (Or.inl rfl) h_Ma_empty
      use τ, τ, D.erase b, D.erase a
      constructor
      · intro h_pair_eq
        have h_erasure_eq : D.erase b = D.erase a := congr_arg Prod.snd h_pair_eq
        have h_a_in_erase_b : a ∈ D.erase b := Finset.mem_erase.mpr ⟨hab, ha_mem⟩
        rw [h_erasure_eq] at h_a_in_erase_b
        exact (Finset.notMem_erase a D) h_a_in_erase_b
      constructor
      · exact h_room_b
      constructor
      · exact h_room_a
      constructor
      · exact h_door_b
      constructor
      · exact h_door_a
      · intros σ C h_room h_door_rel
        rcases incident_room_eq_of_both_M_empty τ D a b h_door h_nonempty ha_mem
            hb_mem hab h_eq_mini h_Ma_empty h_Mb_empty σ C h_room h_door_rel with
          hA | hB
        · exact Or.inr hA
        · exact Or.inl hB


end KeyLemma


noncomputable section Scarf

open Classical


--variable [IST : IndexedLOrder I T]

variable (c : T → I) (σ : Finset T) (C : Finset I)

def isColorful : Prop := IST.isCell σ C ∧ σ.image c   = C

def isNearlyColorful : Prop := IST.isCell σ C ∧ (C \ σ.image c).card = 1

def isTypedNC (i : I) (σ : Finset T) (C : Finset I): Prop := IST.isCell σ C ∧ (C \ (σ.image c)) = {i}


variable {c σ C}


omit [Inhabited T] [DecidableEq T] in
lemma not_colorful_of_TypedNC (h1 : isTypedNC c i σ C) : ¬ IST.isColorful c σ C := by
  intro h
  unfold isTypedNC at h1
  unfold isColorful at h
  have h_diff := h1.2
  have h_ne : σ.image c ≠ C := by
    intro h_eq
    rw [←h_eq, Finset.sdiff_self] at h_diff
    have h_singleton_nonempty : ({i} : Finset I).Nonempty := Finset.singleton_nonempty i
    rw [←h_diff] at h_singleton_nonempty
    exact Finset.not_nonempty_empty h_singleton_nonempty
  exact h_ne h.2

omit [Inhabited T] [DecidableEq T] in
lemma NC_of_TNC (h1 : isTypedNC c i σ C) : isNearlyColorful c σ C := by
  have hcell := h1.1
  have heq := h1.2
  constructor
  · exact hcell
  · rw [heq]
    have h_eq : C \ image c σ = {i} := by
      rw [heq]
    rw [←heq, h_eq]
    exact Finset.card_singleton i


lemma Finset.eq_of_mem_of_card_one {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (h_mem : a ∈ s) (h_card : s.card = 1) : s = {a} :=
  Finset.eq_singleton_iff_unique_mem.mpr ⟨h_mem, fun y hy =>
    let ⟨b, hb⟩ := Finset.card_eq_one.mp h_card
    have h_a_eq_b : a = b := Finset.eq_of_mem_singleton (hb ▸ h_mem)
    have h_y_eq_b : y = b := Finset.eq_of_mem_singleton (hb ▸ hy)
    h_y_eq_b.trans h_a_eq_b.symm⟩

omit [Inhabited T] [DecidableEq T] in
lemma room_of_colorful (h : IST.isColorful c σ C) : IST.isRoom σ C := by
  unfold isRoom
  unfold isColorful at h
  constructor
  · exact h.1
  · have h1 : C.card = (σ.image c).card := by rw [h.2]
    have h2 : (σ.image c).card ≤ σ.card := Finset.card_image_le
    have h3 : σ.card ≤ C.card := card_le_of_isDominant h.1
    linarith



def pick_colorful_point (h : IST.isColorful c σ C): σ := Classical.choice (sigma_nonempty_of_room (room_of_colorful h)).to_subtype


-- Easy
/- Lemma 4 -/
omit [Inhabited T] [DecidableEq T] in
lemma NC_of_outsidedoor (h : isOutsideDoor σ C) : isNearlyColorful c σ C  := by
  cases h with
  | intro hd he =>
    unfold isNearlyColorful
    unfold isCell
    constructor
    · exact hd.1
    · rw [he]
      have h_img : Finset.image c Finset.empty = Finset.empty := Finset.image_empty c
      rw [h_img]
      have h_disj : Disjoint C Finset.empty := Finset.disjoint_empty_right C
      have h_sdiff : C \ Finset.empty = C := Finset.sdiff_eq_self_of_disjoint h_disj
      rw [h_sdiff]
      unfold isDoor at hd
      have h1 := hd.2
      rw [he] at h1
      exact h1

/-Lemma 5-/
omit [Inhabited T] in
lemma NC_or_C_of_door (h1 : isTypedNC c i τ D) (h2 : isDoorof τ D σ C) : isTypedNC c i σ C ∨ isColorful c σ C := by
  unfold isTypedNC at h1 ⊢
  unfold isColorful
  have h1_cell := h1.left
  have h1_eq := h1.right

  have h_sigma_cell : isCell σ C := by
    cases h2 with
    | idoor h0 _ _ _ _ _ => exact h0
    | odoor h0 _ _ _ _ _ => exact h0

  have step1_subset : C \ (σ.image c) ⊆ D \ (τ.image c) := by
    intro y hy
    simp only [Finset.mem_sdiff] at hy ⊢
    obtain ⟨y_in_C, y_notin_img_sigma⟩ := hy
    constructor
    · cases h2
      · rename_i h_D_eq; rw [h_D_eq]; exact y_in_C
      · rename_i h_D_eq; rw [h_D_eq]; exact Finset.mem_insert_of_mem y_in_C
    · cases h2 with
      | idoor h0 hdoor x h_x_notin h_sigma_eq h_D_eq =>
        rw [← h_sigma_eq, Finset.image_insert] at y_notin_img_sigma
        simp only [Finset.mem_insert, not_or] at y_notin_img_sigma
        exact y_notin_img_sigma.2
      | odoor h0 hdoor j h_j_notin h_sigma_eq h_D_eq =>
        rw [← h_sigma_eq] at y_notin_img_sigma
        exact y_notin_img_sigma

  have step2_D_card : (D \ (τ.image c)).card = 1 := by
    have D_sdiff_eq_i : D \ (τ.image c) = {i} := by
      rw [h1_eq]
    rw [D_sdiff_eq_i, Finset.card_singleton]

  have step3_C_card_le : (C \ σ.image c).card ≤ 1 := by
    rw [← step2_D_card]
    exact Finset.card_le_card step1_subset

  by_cases h : (C \ σ.image c).card = 0
  · right
    constructor
    · exact h_sigma_cell
    · have h_C_subset_img : C ⊆ σ.image c := by
        rw [Finset.subset_iff]
        intro x hx
        by_contra hxn
        have : x ∈ C \ σ.image c := by simp [hx, hxn]
        have : (C \ σ.image c).Nonempty := ⟨x, this⟩
        have : 0 < (C \ σ.image c).card := Finset.card_pos.2 this
        linarith [h]

      have h_room: isRoom σ C := isRoom_of_Door h2
      have h_card_eq : C.card = σ.card := h_room.2
      have h_img_le_C_card : (σ.image c).card ≤ C.card := by
        calc (σ.image c).card
          ≤ σ.card := Finset.card_image_le
          _ = C.card := h_card_eq.symm
      exact (Finset.eq_of_subset_of_card_le h_C_subset_img h_img_le_C_card).symm

  · left
    constructor
    · exact h_sigma_cell
    · have h_card_one : (C \ σ.image c).card = 1 := by omega

      have h_subset_singleton : C \ σ.image c ⊆ {i} := by
        have D_sdiff_eq_i : D \ (τ.image c) = {i} := by
          rw [h1_eq]
        rw [← D_sdiff_eq_i]
        exact step1_subset

      have C_sdiff_eq_i : C \ σ.image c = {i} :=
        Finset.eq_of_subset_of_card_le h_subset_singleton (by rw [h_card_one, Finset.card_singleton])

      have h_i_notin_img : i ∉ σ.image c := by
        have h_i_in_sdiff : i ∈ C \ σ.image c := by rw [C_sdiff_eq_i]; simp
        exact (Finset.mem_sdiff.mp h_i_in_sdiff).2

      exact C_sdiff_eq_i

omit [Inhabited T] in
lemma isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC (h_nc : isNearlyColorful c τ D) (h_door : isDoorof τ D σ C) (h_room_typed : isTypedNC c i σ C) : isTypedNC c i τ D := by
  constructor
  · exact h_nc.1
  · have h_subset : C \ image c σ ⊆ D \ image c τ := by
      intro y hy
      simp only [Finset.mem_sdiff] at hy ⊢
      obtain ⟨y_in_C, y_notin_img_sigma⟩ := hy
      constructor
      · cases h_door with
        | idoor h0 _ _ _ _ h_D_eq => rw [h_D_eq]; exact y_in_C
        | odoor h0 _ _ _ _ h_D_eq => rw [h_D_eq]; exact Finset.mem_insert_of_mem y_in_C
      · cases h_door with
        | idoor h0 _ x _ h_sigma_eq _ =>
          rw [← h_sigma_eq, Finset.image_insert] at y_notin_img_sigma
          simp only [Finset.mem_insert, not_or] at y_notin_img_sigma
          exact y_notin_img_sigma.2
        | odoor h0 _ _ _ h_sigma_eq _ =>
          rw [← h_sigma_eq] at y_notin_img_sigma
          exact y_notin_img_sigma
    have h_i_in_diff : i ∈ D \ image c τ := h_subset (h_room_typed.2 ▸ Finset.mem_singleton_self i)
    have h_card_one : (D \ image c τ).card = 1 := h_nc.2
    exact Finset.eq_of_mem_of_card_one h_i_in_diff h_card_one

/- Lemma 6 -/
omit [Inhabited T] [DecidableEq T] in
lemma card_of_NCcell (h : isNearlyColorful c σ D) : #σ = #(image c σ)  ∨  #σ = #(image c σ) + 1 := by
  unfold isNearlyColorful at h
  rcases h with ⟨h_cell, h_nc_card⟩
  let img := image c σ
  have h_card_le_D : σ.card ≤ D.card := card_le_of_isDominant h_cell
  have h_D_card_eq := (Finset.card_sdiff_add_card_inter D img).symm
  rw [h_nc_card] at h_D_card_eq
  have h_inter_le_img : (D ∩ img).card ≤ img.card := card_le_card (Finset.inter_subset_right)
  have h_D_le : D.card ≤ 1 + img.card := by
    linarith [h_D_card_eq, h_inter_le_img]
  have h_img_le_sigma : img.card ≤ σ.card := card_image_le
  have h_sigma_le_plus_one : σ.card ≤ img.card + 1 := by
    linarith [h_card_le_D, h_D_le]
  have h_or : σ.card ≤ img.card ∨ σ.card = img.card + 1 := by
    apply Nat.le_or_eq_of_le_succ
    exact h_sigma_le_plus_one
  cases h_or with
  | inl h_le =>
    left
    exact le_antisymm h_le h_img_le_sigma
  | inr h_eq =>
    right
    exact h_eq

omit [Inhabited T] [DecidableEq T] in
lemma image_subset_of_NCdoor (h1 : isNearlyColorful c σ C) (h2 : isDoor σ C) : image c σ ⊆ C := by
  unfold isNearlyColorful at h1
  unfold isDoor at h2
  rcases h1 with ⟨h_cell, h_nc_card⟩
  rcases h2 with ⟨_, h_door_card⟩
  let img := image c σ
  have h_img_le_sigma : img.card ≤ σ.card := card_image_le
  have h_sigma_le_C : σ.card ≤ C.card := card_le_of_isDominant h_cell
  have h_inter_card : (C ∩ img).card = σ.card := by
    have h_C_card_eq := (Finset.card_sdiff_add_card_inter C img).symm
    rw [h_nc_card] at h_C_card_eq
    have h_C_eq : C.card = 1 + (C ∩ img).card := by linarith [h_C_card_eq]
    rw [h_door_card] at h_C_eq
    linarith [h_C_eq]
  have h_img_eq_inter : img.card = (C ∩ img).card := by
    have h_le1 : (C ∩ img).card ≤ img.card := card_le_card (Finset.inter_subset_right)
    have h_le2 : img.card ≤ (C ∩ img).card := by
      calc img.card
        ≤ σ.card := h_img_le_sigma
        _ = (C ∩ img).card := h_inter_card.symm
    exact le_antisymm h_le2 h_le1
  have h_inter_eq_img : C ∩ img = img :=
    Finset.eq_of_subset_of_card_le (Finset.inter_subset_right) (by rw [h_img_eq_inter])
  rwa [Finset.inter_eq_right] at h_inter_eq_img

section ImageErase

variable {T I : Type*} [DecidableEq T] [DecidableEq I]

lemma image_erase_eq_erase_image_of_unique
  (σ : Finset T) (c : T → I) {z : T}
  (_ : z ∈ σ)
  (uniq : ∀ ⦃w⦄, w ∈ σ → c w = c z → w = z) :
  (σ.erase z).image c = (σ.image c).erase (c z) := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨w, hw_in_erase, rfl⟩
    rcases Finset.mem_erase.mp hw_in_erase with ⟨hw_ne_z, hw_in_σ⟩
    have h_ne_color : c w ≠ c z := by
      intro h_eq
      have := uniq hw_in_σ h_eq
      exact hw_ne_z this
    exact Finset.mem_erase.mpr ⟨h_ne_color, Finset.mem_image.mpr ⟨w, hw_in_σ, rfl⟩⟩
  · intro hi
    rcases Finset.mem_erase.mp hi with ⟨h_i_ne, hi_img⟩
    rcases Finset.mem_image.mp hi_img with ⟨w, hw_in_σ, rfl⟩
    have hw_ne_z : w ≠ z := by
      intro h_eq
      apply h_i_ne
      simp [h_eq]
    exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hw_ne_z, hw_in_σ⟩, rfl⟩

end ImageErase
variable (c σ C) in
abbrev NCdoors := {(τ,D) | isNearlyColorful c τ D ∧ isDoorof τ D σ C }


omit [DecidableEq T] [Inhabited T] IST in
lemma three_collision_card_bound [DecidableEq T] (σ : Finset T) (c : T → I)
    (a b z : T) (ha_in_σ : a ∈ σ) (hb_in_σ : b ∈ σ) (hz_in_σ : z ∈ σ)
    (hab_ne : a ≠ b) (haz_ne : a ≠ z) (hbz_ne : b ≠ z)
    (hc_eq : c a = c b) (hcz_eq : c b = c z) :
    σ.card ≥ (σ.image c).card + 2 := by
  let σ_rest := σ \ {a, b, z}
  have h_three_subset_sigma : {a, b, z} ⊆ σ := by
    intro w hw; simp at hw; rcases hw with (rfl | rfl | rfl);
    · exact ha_in_σ
    · exact hb_in_σ
    · exact hz_in_σ

  have h_partition : σ = {a, b, z} ∪ σ_rest :=
    (Finset.union_sdiff_of_subset h_three_subset_sigma).symm

  have h_disjoint : Disjoint ({a, b, z} : Finset T) σ_rest :=
    Finset.disjoint_sdiff

  have h_card_partition : σ.card = ({a, b, z} : Finset T).card + σ_rest.card := by
    rw [h_partition, Finset.card_union_of_disjoint h_disjoint]

  have h_triple_card : ({a, b, z} : Finset T).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨a, b, z, hab_ne, haz_ne, hbz_ne, rfl⟩

  have h_image_bound : (σ.image c).card ≤ σ_rest.card + 1 := by
    have h_image_union : σ.image c = insert (c a) (σ_rest.image c) := by
      ext i; simp only [Finset.mem_image, Finset.mem_insert]
      constructor
      · rintro ⟨t, ht_in_σ, rfl⟩
        by_cases h_t_abz : t ∈ ({a, b, z} : Finset T)
        · simp at h_t_abz; rcases h_t_abz with (rfl | rfl | rfl)
          · left; rfl
          · left; exact hc_eq.symm
          · left; exact (hc_eq.trans hcz_eq).symm
        · right; use t; simp [σ_rest, ht_in_σ, h_t_abz]
      · rintro (rfl | ⟨t, ht_in_rest, rfl⟩)
        · use a
        · use t; exact ⟨(Finset.mem_sdiff.mp ht_in_rest).1, rfl⟩
    rw [h_image_union]
    linarith [Finset.card_insert_le (c a) (σ_rest.image c), Finset.card_image_le (f := c) (s := σ_rest)]

  calc σ.card
      = 3 + σ_rest.card           := by rw [h_card_partition, h_triple_card]
    _ = σ_rest.card + 3           := by ring
    _ = (σ_rest.card + 1) + 2     := by ring
    _ ≥ (σ.image c).card + 2      := by omega


omit [DecidableEq T] [Inhabited T] IST in
lemma image_erase_eq_of_exists_other [DecidableEq T] (σ : Finset T) (c : T → I)
    (x y : T) (_hx_in_σ : x ∈ σ) (hy_in_σ : y ∈ σ) (hxy_ne : x ≠ y)
    (hcxy_eq : c x = c y) :
    (σ.erase x).image c = σ.image c := by
  ext z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, hw_in_erased, rfl⟩
    exact ⟨w, (Finset.mem_erase.mp hw_in_erased).2, rfl⟩
  · rintro ⟨w, hw_in_σ, rfl⟩
    by_cases hwx : w = x
    · subst w
      exact ⟨y, Finset.mem_erase.mpr ⟨hxy_ne.symm, hy_in_σ⟩, hcxy_eq.symm⟩
    · exact ⟨w, Finset.mem_erase.mpr ⟨hwx, hw_in_σ⟩, rfl⟩

omit [DecidableEq T] [Inhabited T] IST in
lemma image_erase_collision_preserves [DecidableEq T] (σ : Finset T) (c : T → I)
    (x y : T) (hx_in_σ : x ∈ σ) (hy_in_σ : y ∈ σ) (hxy_ne : x ≠ y) (hcxy_eq : c x = c y) :
    (σ.erase x).image c = σ.image c ∧ (σ.erase y).image c = σ.image c := by
  exact ⟨
    image_erase_eq_of_exists_other σ c x y hx_in_σ hy_in_σ hxy_ne hcxy_eq,
    image_erase_eq_of_exists_other σ c y x hy_in_σ hx_in_σ hxy_ne.symm hcxy_eq.symm⟩


omit [DecidableEq T] [Inhabited T] in
lemma isDoorof_erase_of_isRoom [DecidableEq T] (σ : Finset T) (C : Finset I)
    (x : T) (h_room : isRoom σ C) (hx_in_σ : x ∈ σ) :
    isDoorof (σ.erase x) C σ C := by
  apply isDoorof.idoor h_room.1
  · constructor
    · exact Dominant_of_subset σ (σ.erase x) C (Finset.erase_subset x σ) h_room.1
    · rw [h_room.2]
      rw [Finset.card_erase_of_mem hx_in_σ]
      exact (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨x, hx_in_σ⟩)).symm
  · exact Finset.notMem_erase x σ
  · exact Finset.insert_erase hx_in_σ
  · rfl

omit [DecidableEq T] [Inhabited T] in
lemma image_subset_of_NCroom_of_card_image_add_one [DecidableEq T]
    (h_room : isRoom σ C) (h_nc : isNearlyColorful c σ C)
    (h_card : σ.card = (σ.image c).card + 1) :
    σ.image c ⊆ C := by
  have h_C_card_img : C.card = (σ.image c).card + 1 := by
    rw [h_room.2, h_card]
  have h_C_card_form :
      C.card = (C \ σ.image c).card + (C ∩ σ.image c).card :=
    (Finset.card_sdiff_add_card_inter C (σ.image c)).symm
  rw [h_nc.2] at h_C_card_form
  have h_img_eq_inter_card : (σ.image c).card = (C ∩ σ.image c).card := by
    omega
  have h_inter_eq_img : C ∩ σ.image c = σ.image c :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [h_img_eq_inter_card])
  rwa [Finset.inter_eq_right] at h_inter_eq_img

-- Lemma 7
omit [DecidableEq T] [Inhabited T] in
lemma doors_of_NCroom [DecidableEq T] (h_room : isRoom σ C) (h_nc : isNearlyColorful c σ C) :
  ∃ door1 door2, door1 ≠ door2 ∧ NCdoors c σ C = {door1, door2} := by
  have h_cases := card_of_NCcell h_nc
  have h_card_eq : C.card = σ.card := h_room.2
  have h_cell : isCell σ C := h_room.1
  let img := image c σ

  cases h_cases with
  | inl h_eq =>
    have h_inj_on_σ : Set.InjOn c ↑σ := (Finset.card_image_iff).mp h_eq.symm
    have h_img_C_card_1 : (img \ C).card = 1 := by
      have h_card_eq' : C.card = img.card := by linarith [h_card_eq, h_eq]
      have h_C_sdiff := Finset.card_sdiff_add_card_inter C img
      rw [h_nc.2, h_card_eq'] at h_C_sdiff
      have h_img_sdiff := Finset.card_sdiff_add_card_inter img C
      rw [Finset.inter_comm] at h_C_sdiff
      linarith [h_C_sdiff, h_img_sdiff]
    obtain ⟨c_y, h_img_C_eq⟩ := Finset.card_eq_one.mp h_img_C_card_1
    have h_c_y_in_img : c_y ∈ img := by
      have : c_y ∈ img \ C := by rw [h_img_C_eq]; simp
      exact (Finset.mem_sdiff.mp this).1
    have h_c_y_notin_C : c_y ∉ C := by
      have : c_y ∈ img \ C := by rw [h_img_C_eq]; simp
      exact (Finset.mem_sdiff.mp this).2
    obtain ⟨y, h_y_in_σ, h_c_y_eq⟩ := Finset.mem_image.mp h_c_y_in_img
    subst h_c_y_eq
    have h_y_unique : ∀ ⦃z⦄, z ∈ σ → c z = c y → z = y :=
      λ z hz hcz => h_inj_on_σ hz h_y_in_σ hcz
    let door1 := (σ.erase y, C)
    let door2 := (σ, insert (c y) C)
    use door1, door2
    constructor
    · intro h_eq_doors; simp [Prod.ext_iff] at h_eq_doors;
      have this := h_eq_doors.1
      have : y ∉ σ := Finset.erase_eq_self.mp this
      exact this h_y_in_σ
    · ext ⟨τ, D⟩; constructor
      · intro h
        rcases h with ⟨h_nc_door, h_is_door⟩
        cases h_is_door with
        | idoor h0 h_door x hx_notin_τ h_insert_x h_D_eq_C =>
          subst h_D_eq_C
          have h_nc_card := h_nc_door.2
          have h_x_in_σ : x ∈ σ := by rw [←h_insert_x]; exact Finset.mem_insert_self x τ
          have h_τ_eq_erase : τ = σ.erase x := by rw [←Finset.erase_insert hx_notin_τ, h_insert_x]
          have h_x_unique : ∀ ⦃w⦄, w ∈ σ → c w = c x → w = x := by
            intro w hw hcw
            exact h_inj_on_σ hw h_x_in_σ hcw
          have h_img_erase : (τ.image c) = img.erase (c x) := by
            rw [h_τ_eq_erase]
            exact image_erase_eq_erase_image_of_unique σ c h_x_in_σ h_x_unique
          rw [h_img_erase] at h_nc_card
          by_cases h_x_eq_y : x = y
          · subst h_x_eq_y
            simp [h_τ_eq_erase, door1]
          · have h_cx_in_D : c x ∈ D := by
              by_contra h_cx_notin_C
              have h_cx_in_img_diff_D : c x ∈ img \ D := Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem c h_x_in_σ, h_cx_notin_C⟩
              rw [h_img_C_eq, Finset.mem_singleton] at h_cx_in_img_diff_D
              have h_c_eq : c x = c y := by rw [h_cx_in_img_diff_D]
              have x_in_sigma : x ∈ σ := by
                have : x ∈ insert x τ := Finset.mem_insert_self x τ
                have : x ∈ σ := by
                  rw [←h_insert_x]
                  exact Finset.mem_insert_self x τ
                exact this
              have := h_y_unique x_in_sigma h_c_eq
              exact h_x_eq_y this
            exfalso
            have h_card_2 : (D \ (img.erase (c x))).card = 2 := by
              have h_cx_not_in_diff : c x ∉ D \ img := by
                intro h
                exact (Finset.mem_sdiff.mp h).2 (Finset.mem_image_of_mem c h_x_in_σ)
              rw [Finset.sdiff_erase h_cx_in_D,
                Finset.card_insert_of_notMem h_cx_not_in_diff, h_nc.2]
            rw [h_card_2] at h_nc_card; linarith
           | odoor h0 h_door j hj_notin_C h_τ_eq_σ h_D_eq_insert =>
            subst h_τ_eq_σ; subst h_D_eq_insert
            have h_nc_card := h_nc_door.2
            by_cases h_j_eq_cy : j = c y
            · subst h_j_eq_cy; simp; right; rfl
            · exfalso
              have h_j_notin_img : j ∉ img := by
                intro h_j_in_img
                have h_j_in_img_diff_C : j ∈ img \ C := Finset.mem_sdiff.mpr ⟨h_j_in_img, hj_notin_C⟩
                rw [h_img_C_eq, Finset.mem_singleton] at h_j_in_img_diff_C
                exact h_j_eq_cy h_j_in_img_diff_C
              have h_card_2 : ((insert j C) \ img).card = 2 := by
                have h_j_notin_diff : j ∉ C \ img := fun h =>
                  hj_notin_C (Finset.mem_sdiff.mp h).1
                rw [Finset.insert_sdiff_of_notMem C h_j_notin_img,
                  Finset.card_insert_of_notMem h_j_notin_diff, h_nc.2]
              rw [h_card_2] at h_nc_card; linarith
      · intro h
        simp at h
        rcases h with (h_eq1 | h_eq2)
        · have ⟨h_τ_eq, h_D_eq⟩ : τ = σ.erase y ∧ D = C := Prod.mk.inj h_eq1
          subst h_τ_eq h_D_eq
          constructor
          · unfold isNearlyColorful
            constructor
            · unfold isCell
              exact Dominant_of_subset _ _ D (Finset.erase_subset y σ) h_cell
            · rw [image_erase_eq_erase_image_of_unique σ c h_y_in_σ h_y_unique]
              have h_eq_diff : D \ (image c σ).erase (c y) = D \ image c σ := by
                ext z
                constructor
                · intro h
                  simp only [Finset.mem_sdiff, Finset.mem_erase] at h ⊢
                  exact ⟨h.1, fun h_in => h.2 ⟨fun h_eq => h_c_y_notin_C (h_eq ▸ h.1), h_in⟩⟩
                · intro h
                  simp only [Finset.mem_sdiff, Finset.mem_erase] at h ⊢
                  exact ⟨h.1, fun ⟨_, h_in⟩ => h.2 h_in⟩
              rw [h_eq_diff, h_nc.2]
          · apply isDoorof.idoor
            · exact h_cell
            · constructor
              · unfold isCell
                exact Dominant_of_subset _ _ D (Finset.erase_subset y σ) h_cell
              · rw [Finset.card_erase_of_mem h_y_in_σ, h_card_eq]
                exact (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨y, h_y_in_σ⟩)).symm
            · exact Finset.notMem_erase y σ
            · exact Finset.insert_erase h_y_in_σ
            · rfl

        · have ⟨h_τ_eq, h_D_eq⟩ : τ = σ ∧ D = insert (c y) C := Prod.mk.inj h_eq2
          subst h_τ_eq h_D_eq
          constructor
          · unfold isNearlyColorful
            constructor
            · unfold isCell
              unfold isDominant
              intro z
              obtain ⟨i, hi_in_C, hi_dom⟩ := h_cell z
              use i, Finset.mem_insert_of_mem hi_in_C
            · have h_j_in_img : c y ∈ img := Finset.mem_image_of_mem c h_y_in_σ
              have h_sdiff_insert : (insert (c y) C) \ img = C \ img := by
                rw [Finset.insert_sdiff_of_mem _ h_j_in_img]
              rw [h_sdiff_insert, h_nc.2]
          · apply isDoorof.odoor
            · exact h_cell
            · constructor
              · apply Dominant_of_supset τ C (insert (c y) C)
                · exact Finset.subset_insert (c y) C
                · exact h_cell
              · rw [Finset.card_insert_of_notMem h_c_y_notin_C, h_card_eq]
            · exact h_c_y_notin_C
            · rfl
            · rfl
  | inr h_inj =>
    have h_img_subset_C : image c σ ⊆ C :=
      image_subset_of_NCroom_of_card_image_add_one h_room h_nc h_inj
    unfold isNearlyColorful at h_nc
    obtain ⟨h_cell, h_missing_card⟩ := h_nc
    obtain ⟨x, y, h_x_in_σ, h_y_in_σ, h_cxy_eq, h_xy_ne, h_inj_outside⟩ :=
      injOn_sdiff σ c h_inj

    let τ₁ := σ.erase x
    let τ₂ := σ.erase y
    let door1 := (τ₁, C)
    let door2 := (τ₂, C)

    have h_door1_valid : isDoorof τ₁ C σ C :=
      isDoorof_erase_of_isRoom σ C x h_room h_x_in_σ

    have h_door2_valid : isDoorof τ₂ C σ C :=
      isDoorof_erase_of_isRoom σ C y h_room h_y_in_σ

    have h_imgs_preserved := image_erase_collision_preserves σ c x y h_x_in_σ h_y_in_σ h_xy_ne h_cxy_eq

    have h_door1_nc : isNearlyColorful c τ₁ C := by
      unfold isNearlyColorful
      constructor
      · exact Dominant_of_subset σ τ₁ C (Finset.erase_subset x σ) h_cell
      · rw [h_imgs_preserved.1, h_missing_card]

    have h_door2_nc : isNearlyColorful c τ₂ C := by
      unfold isNearlyColorful
      constructor
      · exact Dominant_of_subset σ τ₂ C (Finset.erase_subset y σ) h_cell
      · rw [h_imgs_preserved.2, h_missing_card]

    have h_doors_distinct : door1 ≠ door2 := by
      simp [door1, door2, τ₁, τ₂]
      intro h_eq
      have h_y_mem : y ∈ σ.erase x := by
        rw [Finset.mem_erase]
        exact ⟨h_xy_ne.symm, h_y_in_σ⟩
      rw [h_eq] at h_y_mem
      have h_y_not_mem : y ∉ σ.erase y := by
        rw [Finset.mem_erase]
        simp
      exact h_y_not_mem h_y_mem

    have h_exactly_two : NCdoors c σ C = {door1, door2} := by
      ext ⟨τ, D⟩
      simp [NCdoors]
      constructor
      · intro ⟨h_nc_τD, h_door_τD⟩
        cases h_door_τD with
        | idoor h_cell_σC h_door_τD z h_z_notin_τ h_insert_eq h_D_eq_C =>
          rw [h_D_eq_C]
          have h_τ_eq : τ = σ.erase z := by
            rw [←Finset.erase_insert h_z_notin_τ, h_insert_eq]
          rw [h_τ_eq]
          have h_z_in_σ : z ∈ σ := by
            rw [←h_insert_eq]
            exact Finset.mem_insert_self z τ
          by_cases h_z_cases : z = x ∨ z = y
          · rcases h_z_cases with h_z_eq_x | h_z_eq_y
            · left; simp [door1, τ₁, h_z_eq_x]
            · right; simp [door2, τ₂, h_z_eq_y]
          · exfalso
            push Not at h_z_cases
            have h_card_is_one : (C \ (σ.erase z).image c).card = 1 := by rw [←h_D_eq_C, ←h_τ_eq]; exact h_nc_τD.2
            have h_card_is_two : (C \ (σ.erase z).image c).card = 2 := by
              have h_uniq_z : ∀ w ∈ σ, c w = c z → w = z := by
                intro w hw hcw
                have hw_not_pair : w ∉ ({x, y} : Finset T) := by
                  intro hw_pair
                  have hcyz : c y = c z := by
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hw_pair
                    rcases hw_pair with rfl | rfl
                    · exact h_cxy_eq.symm.trans hcw
                    · exact hcw
                  have h_card_ge_img_add_2 :
                      σ.card ≥ (σ.image c).card + 2 :=
                    three_collision_card_bound σ c x y z h_x_in_σ h_y_in_σ h_z_in_σ
                      h_xy_ne h_z_cases.1.symm h_z_cases.2.symm h_cxy_eq hcyz
                  omega
                have hw_sdiff : w ∈ σ \ {x, y} :=
                  Finset.mem_sdiff.mpr ⟨hw, hw_not_pair⟩
                have hz_sdiff : z ∈ σ \ {x, y} :=
                  Finset.mem_sdiff.mpr ⟨h_z_in_σ, by simpa using h_z_cases⟩
                exact h_inj_outside (by simpa using hw_sdiff) (by simpa using hz_sdiff) hcw

              have h_img_erase : (σ.erase z).image c = (σ.image c).erase (c z) :=
                image_erase_eq_erase_image_of_unique σ c h_z_in_σ h_uniq_z

              have h_cz_in_C : c z ∈ C := h_img_subset_C (mem_image_of_mem c h_z_in_σ)
              have h_cz_not_in_diff : c z ∉ C \ image c σ := by simp [mem_image_of_mem c h_z_in_σ]
              rw [h_img_erase, Finset.sdiff_erase h_cz_in_C,
                Finset.card_insert_of_notMem h_cz_not_in_diff, h_missing_card]

            rw [h_card_is_two] at h_card_is_one
            norm_num at h_card_is_one

        | odoor h_cell_σC h_door_τD j h_j_notin_C h_τ_eq_σ h_D_eq =>
          exfalso
          have h_card_is_one : ((insert j C) \ σ.image c).card = 1 := by
            rw [← h_D_eq, ← h_τ_eq_σ]
            exact h_nc_τD.2
          have h_j_notin_img : j ∉ image c σ := fun h => h_j_notin_C (h_img_subset_C h)
          have h_card_is_two : ((insert j C) \ σ.image c).card = 2 := by
            have h_j_notin_diff : j ∉ C \ σ.image c := fun h =>
              h_j_notin_C (Finset.mem_sdiff.mp h).1
            rw [Finset.insert_sdiff_of_notMem C h_j_notin_img,
              Finset.card_insert_of_notMem h_j_notin_diff, h_missing_card]
          rw [h_card_is_two] at h_card_is_one
          norm_num at h_card_is_one
      · intro h_or
        cases h_or with
        | inl h_eq =>
          have : τ = τ₁ ∧ D = C := Prod.mk.inj h_eq
          rw [this.1, this.2]
          exact ⟨h_door1_nc, h_door1_valid⟩
        | inr h_eq =>
          have : τ = τ₂ ∧ D = C := Prod.mk.inj h_eq
          rw [this.1, this.2]
          exact ⟨h_door2_nc, h_door2_valid⟩

    use door1, door2


variable [Fintype T] [Fintype I]

variable (c) in
abbrev colorful := Finset.filter (fun (x : Finset T× Finset I) =>  IST.isColorful c x.1 x.2) univ

variable (c) in
abbrev doubleCountingSet (i : I) :=
  Finset.filter (fun x : (Finset T × Finset I) × (Finset T × Finset I) =>
    isTypedNC c i x.1.1 x.1.2 ∧ isDoorof x.1.1 x.1.2 x.2.1 x.2.2) univ


variable (c) in
lemma exists_filter_isOutsideDoor_eq_singleton (i : I) :
    ∃ x, filter (fun x => isOutsideDoor x.1.1 x.1.2) (doubleCountingSet c i) = {x} := by
  classical

  have h_T_nonempty : Nonempty T := ⟨(default : T)⟩
  have h_T_univ_nonempty : (Finset.univ : Finset T).Nonempty := Finset.univ_nonempty_iff.mpr h_T_nonempty
  let x_max_i : T := @Finset.max' T (IST i) Finset.univ h_T_univ_nonempty
  let σ_u : Finset T := {x_max_i}
  let C_u : Finset I := {i}
  let τ_u : Finset T := Finset.empty
  let D_u : Finset I := {i}
  let x_unique : (Finset T × Finset I) × (Finset T × Finset I) := ((τ_u, D_u), (σ_u, C_u))

  have h_outside_door_τu_Du : isOutsideDoor τ_u D_u := outsidedoor_singleton i
  have h_typed_nc : isTypedNC c i τ_u D_u := by
    constructor
    · exact (NC_of_outsidedoor (c := c) h_outside_door_τu_Du).1
    · simp only [τ_u]
      constructor

  have h_door_relation : isDoorof τ_u D_u σ_u C_u := by
    apply isDoorof.idoor
    · intro y
      use i
      constructor
      · simp only [C_u, Finset.mem_singleton]
      · intro x hx
        simp only [σ_u] at hx
        simp only [Finset.mem_singleton] at hx
        rw [hx]
        exact @Finset.le_max' T (IST i) Finset.univ y (Finset.mem_univ y)
    · exact h_outside_door_τu_Du.1
    · simp only [τ_u]
      exact Finset.notMem_empty x_max_i
    · simp only [τ_u, σ_u]
      rfl
    · rfl

  use x_unique
  ext x_gen
  simp only [mem_filter, mem_univ, mem_singleton]

  constructor
  · intro h_in_filter
    simp at h_in_filter
    obtain ⟨h_in_db, h_outside⟩ := h_in_filter
    obtain ⟨h_typed, h_door⟩ := h_in_db
    obtain ⟨h_is_door, h_empty⟩ := h_outside
    have h_empty_image : (x_gen.1.1).image c = ∅ := by
      rw [h_empty]
      exact Finset.image_empty c
    have h_x_gen_1_2_eq : x_gen.1.2 = {i} := by
      have h_eq := h_typed.2
      rw [h_empty_image] at h_eq
      simp at h_eq
      exact h_eq
    obtain ⟨_, h_D_singleton⟩ := outsidedoor_is_singleton ⟨h_is_door, h_empty⟩
    obtain ⟨j, h_D_eq⟩ := h_D_singleton

    have h_j_eq_i : j = i := by
      have h_eq_j : x_gen.1.2 = {j} := h_D_eq
      rw [h_x_gen_1_2_eq] at h_eq_j
      have : j ∈ {j} := Finset.mem_singleton_self j
      rw [←h_eq_j] at this
      exact Finset.eq_of_mem_singleton this

    cases h_door with
    | idoor h_cell_σC h_door_τD x h_x_notin h_insert_eq h_D_eq_C =>
      have h_σ_eq : x_gen.2.1 = {x} := by
        rw [←h_insert_eq, h_empty]
        rfl
      have h_x_eq_max : x = x_max_i := by
        have h_dom : ∀ y, y ≤[i] x := by
          intro y
          obtain ⟨j_dom, hj_in, hj_dom⟩ := h_cell_σC y
          rw [←h_D_eq_C, h_x_gen_1_2_eq] at hj_in
          simp at hj_in
          subst hj_in
          apply hj_dom
          rw [h_σ_eq]
          simp
        have h1 : x ≤[i] x_max_i := @Finset.le_max' T (IST i) Finset.univ x (Finset.mem_univ x)
        have h2 : x_max_i ≤[i] x := h_dom x_max_i
        exact @le_antisymm T (IST i).toPartialOrder x x_max_i h1 h2
      apply Prod.ext
      · apply Prod.ext
        · exact h_empty
        · rw [h_x_gen_1_2_eq]
      · apply Prod.ext
        · rw [h_σ_eq, h_x_eq_max]
        · rw [←h_D_eq_C, h_x_gen_1_2_eq]

    | odoor h_cell_σC h_door_τD j h_j_notin h_τ_eq h_D_insert =>
      exfalso
      have h_σ_empty : x_gen.2.1 = ∅ := by
        rw [←h_τ_eq, h_empty]
        rfl
      let h_door_constructed : isDoorof x_gen.1.1 x_gen.1.2 x_gen.2.1 x_gen.2.2 :=
        isDoorof.odoor h_cell_σC ⟨h_is_door.1, h_is_door.2⟩ j h_j_notin h_τ_eq h_D_insert
      have h_room : IST.isRoom x_gen.2.1 x_gen.2.2 := isRoom_of_Door h_door_constructed
      have h_σ_nonempty : x_gen.2.1.Nonempty := sigma_nonempty_of_room h_room
      rw [h_σ_empty] at h_σ_nonempty
      exact Finset.not_nonempty_empty h_σ_nonempty

  · intro h_eq
    rw [h_eq]
    simp only [true_and]
    constructor
    · constructor
      · exact h_typed_nc
      · exact h_door_relation
    · exact h_outside_door_τu_Du

variable (c)

-- Lemma 2
lemma odd_card_filter_isOutsideDoor (i : I) :
    Odd (filter (fun x => isOutsideDoor x.1.1 x.1.2) (doubleCountingSet c i)).card := by
  have h_card_one :
      (filter (fun x => isOutsideDoor x.1.1 x.1.2) (doubleCountingSet c i)).card = 1 := by
    obtain ⟨x, hx⟩ := exists_filter_isOutsideDoor_eq_singleton c i
    simp [hx]
  rw [h_card_one]
  exact odd_one

omit [Inhabited T] in
lemma card_internalDoor_fiber_eq_two (c : T → I) (i : I) (y : Finset T × Finset I)
    (hy_internal : IST.isInternalDoor y.1 y.2) (hy_typed : isTypedNC c i y.1 y.2) :
    let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (doubleCountingSet c i)
    let f := fun (x : (Finset T × Finset I) × Finset T × Finset I) => x.1
    (filter (fun a => f a = y) s).card = 2 := by
  obtain ⟨σ₁, σ₂, C₁, C₂, h_ne, h_room₁, h_room₂, h_door₁, h_door₂, h_unique⟩ :=
    internal_door_two_rooms y.1 y.2 hy_internal
  let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (doubleCountingSet c i)
  let f := fun (x : (Finset T × Finset I) × Finset T × Finset I) => x.1
  let elem1 : (Finset T × Finset I) × Finset T × Finset I := (y, (σ₁, C₁))
  let elem2 : (Finset T × Finset I) × Finset T × Finset I := (y, (σ₂, C₂))
  have elem1_in_s : elem1 ∈ s := by
    simp only [elem1, s, mem_filter]
    constructor
    · simp only [mem_univ, true_and]
      exact ⟨hy_typed, h_door₁⟩
    · intro h_outside
      exact (Finset.nonempty_iff_ne_empty.mp hy_internal.2) h_outside.2
  have elem2_in_s : elem2 ∈ s := by
    simp only [elem2, s, mem_filter]
    constructor
    · simp only [mem_univ, true_and]
      exact ⟨hy_typed, h_door₂⟩
    · intro h_outside
      exact (Finset.nonempty_iff_ne_empty.mp hy_internal.2) h_outside.2
  have elems_distinct : elem1 ≠ elem2 := by
    intro h_eq
    injection h_eq with _ h_pair_eq
    exact h_ne h_pair_eq
  have fiber_eq : filter (fun a => f a = y) s = {elem1, elem2} := by
    ext x
    constructor
    · intro hx
      rw [mem_filter] at hx
      obtain ⟨hx_s, hx_eq⟩ := hx
      rw [mem_filter] at hx_s
      obtain ⟨hx_db, _⟩ := hx_s
      rw [mem_filter] at hx_db
      obtain ⟨_, hx_typed_x, hx_door_x⟩ := hx_db
      have h_x_form : x = (y, x.2) := Prod.ext_iff.mpr ⟨hx_eq, rfl⟩
      have h_room_x2 : IST.isRoom x.2.1 x.2.2 := isRoom_of_Door hx_door_x
      have hx_door_y : isDoorof y.1 y.2 x.2.1 x.2.2 :=
        hx_eq ▸ hx_door_x
      obtain h_case1 | h_case2 := h_unique x.2.1 x.2.2 h_room_x2 hx_door_y
      · simp only [mem_insert, mem_singleton]
        left
        rw [h_x_form]
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact h_case1.1
          · exact h_case1.2
      · simp only [mem_insert, mem_singleton]
        right
        rw [h_x_form]
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact h_case2.1
          · exact h_case2.2
    · intro hx
      simp only [mem_insert, mem_singleton] at hx
      cases hx with
      | inl h =>
        rw [h, mem_filter]
        exact ⟨elem1_in_s, by simp [f, elem1]⟩
      | inr h =>
        rw [h, mem_filter]
        exact ⟨elem2_in_s, by simp [f, elem2]⟩
  apply Eq.trans (congrArg Finset.card fiber_eq)
  exact Finset.card_pair elems_distinct

omit [Inhabited T] in
lemma even_card_filter_not_isOutsideDoor (i : I) :
    Even (filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (doubleCountingSet c i)).card := by
  let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (doubleCountingSet c i)
  let t := filter (fun (x : Finset T × Finset I) => IST.isInternalDoor x.1 x.2 ∧ isTypedNC c i x.1 x.2) univ
  let f := fun (x : (Finset T × Finset I) × Finset T × Finset I) => x.1
  have fs_in_t : ∀ x ∈ s, f x ∈ t := by
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨hx_db, hx_not_outside⟩ := hx
    rw [mem_filter] at hx_db
    obtain ⟨_, hx_typed, hx_door⟩ := hx_db
    rw [mem_filter]
    simp only [mem_univ, true_and]
    constructor
    · unfold isInternalDoor
      constructor
      · cases hx_door with
        | idoor h0 h1 y h_notin h_eq h_D_eq_C => exact h1
        | odoor h0 h1 j h_notin h_eq h_D_eq => exact h1
      · by_contra h_empty
        have h_outside : isOutsideDoor x.1.1 x.1.2 := by
          constructor
          · cases hx_door with
            | idoor h0 h1 y h_notin h_eq h_D_eq_C => exact h1
            | odoor h0 h1 j h_notin h_eq h_D_eq => exact h1
          · exact Finset.not_nonempty_iff_eq_empty.mp h_empty
        exact hx_not_outside h_outside
    · exact hx_typed

  have fiber_size_two : ∀ y ∈ t, (filter (fun a=> f a = y) s).card = 2 := by
    intro y hy
    rw [mem_filter] at hy
    obtain ⟨_, hy_internal, hy_typed⟩ := hy
    exact card_internalDoor_fiber_eq_two c i y hy_internal hy_typed

  have counteq := Finset.card_eq_sum_card_fiberwise fs_in_t
  have sumeq := Finset.sum_const_nat fiber_size_two
  rw [sumeq] at counteq
  rw [counteq]
  simp only [even_two, Even.mul_left]

/- Easy -/
omit [Fintype T] [Fintype I] [Inhabited T] in
variable {c} in
lemma isTypedNC_of_isDoorof_of_not_isColorful (h1 : isTypedNC c i τ D)
    (h2 : isDoorof τ D σ C) :
    ¬ isColorful c σ C → isTypedNC c i σ C := by
  intro h_not_colorful
  obtain h_typed | h_colorful := NC_or_C_of_door h1 h2
  · exact h_typed
  · contradiction

omit [Inhabited T] in
variable {c} in
lemma card_doubleCountingSet_fiber_eq_two (h0 : isRoom σ C) (h1 : isTypedNC c i σ C) :
  (filter (fun (x : (Finset T× Finset I)× Finset T × Finset I) => x.2 = (σ,C)) (doubleCountingSet c i)).card = 2 := by
    obtain ⟨door1, door2, h_ne, h_doors_eq⟩ := doors_of_NCroom h0 (NC_of_TNC h1)
    have h_filter_eq : filter (fun (x : (Finset T× Finset I)× Finset T × Finset I) => x.2 = (σ,C)) (doubleCountingSet c i) =
                       {(door1, (σ,C)), (door2, (σ,C))} := by
      ext x
      constructor
      · intro hx
        rw [mem_filter] at hx
        obtain ⟨h_db, h_eq⟩ := hx
        rw [mem_filter] at h_db
        obtain ⟨_, h_typed, h_door⟩ := h_db
        have h_x_form : x = (x.1, (σ,C)) := by
          rw [Prod.ext_iff]
          exact ⟨rfl, h_eq⟩
        rw [h_x_form]
        simp
        have h_x1_in_doors : x.1 ∈ NCdoors c σ C := by
          simp [NCdoors]
          have h_sigma : x.2.1 = σ := by rw [h_eq]
          have h_C : x.2.2 = C := by rw [h_eq]
          rw [h_sigma, h_C] at h_door
          exact ⟨NC_of_TNC h_typed, h_door⟩
        rw [h_doors_eq] at h_x1_in_doors
        simp at h_x1_in_doors
        exact h_x1_in_doors
      · intro hx
        simp at hx
        cases hx with
        | inl h =>
          rw [h, mem_filter]
          constructor
          · rw [mem_filter]
            have h_door1_in_doors : door1 ∈ NCdoors c σ C := by
              rw [h_doors_eq]
              exact Set.mem_insert door1 {door2}
            simp [NCdoors] at h_door1_in_doors
            exact ⟨by simp, isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC h_door1_in_doors.1 h_door1_in_doors.2 h1, h_door1_in_doors.2⟩
          · rfl
        | inr h =>
          rw [h, mem_filter]
          constructor
          · rw [mem_filter]
            have h_door2_in_doors : door2 ∈ NCdoors c σ C := by
              rw [h_doors_eq]
              exact Set.mem_insert_of_mem door1 (Set.mem_singleton door2)
            simp [NCdoors] at h_door2_in_doors
            exact ⟨by simp, isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC h_door2_in_doors.1 h_door2_in_doors.2 h1, h_door2_in_doors.2⟩
          · rfl
    rw [h_filter_eq]
    simp [h_ne]

omit [Inhabited T] in
lemma even_card_filter_not_isColorful (i : I) :
    Even (filter (fun x => ¬isColorful c x.2.1 x.2.2) (doubleCountingSet c i)).card := by
  let s := filter (fun x => ¬isColorful c x.2.1 x.2.2) (doubleCountingSet c i)
  let t := filter (fun (x : Finset T × Finset I) => IST.isRoom x.1 x.2 ∧ isTypedNC c i x.1 x.2 ) univ
  let f := fun (x : (Finset T × Finset I)× Finset T × Finset I) => x.2
  have fs_in_t : ∀ x ∈ s, f x ∈ t := by
    intro x hx;
    show x.2 ∈ t
    rw [mem_filter] at hx
    obtain ⟨hx1,hx2⟩ := hx
    rw [mem_filter] at hx1
    rw [mem_filter]
    refine ⟨by simp, isRoom_of_Door hx1.2.2,?_⟩
    apply isTypedNC_of_isDoorof_of_not_isColorful hx1.2.1 hx1.2.2 hx2
  have counteq := Finset.card_eq_sum_card_fiberwise fs_in_t
  have fiber_sizetwo :∀ y ∈ t, #(filter (fun a=> f a = y) s) = 2  :=
    by
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨_,hy1,hy2⟩ := hy
      unfold s
      rw [filter_filter]
      have f2 := card_doubleCountingSet_fiber_eq_two hy1 hy2
      rw [<-f2]
      congr 1
      apply filter_congr
      intro x hx
      rw [mem_filter] at hx
      obtain ⟨hx1,hx2,hx3⟩ := hx
      unfold f
      constructor
      · simp
      · intro h
        simp_rw [h,and_true]
        exact not_colorful_of_TypedNC hy2
  have sumeq := Finset.sum_const_nat fiber_sizetwo
  rw [sumeq] at counteq
  rw [counteq]
  simp only [even_two, Even.mul_left]

lemma odd_of_odd_add_even_eq_add_even {a b c d : ℕ}
    (h1 : Odd a) (h2 : Even b) (h3 : Even d) (h4 : a + b = c + d) : Odd c := by
  by_contra h0
  replace h0 := Nat.not_odd_iff_even.1 h0
  have oddab := Even.odd_add h2 h1
  rw [h4] at oddab
  have evencd := Even.add h0 h3
  exact Nat.not_odd_iff_even.2 evencd oddab


lemma odd_card_filter_isColorful (i : I) : Odd (Finset.filter (fun (x: (Finset T× Finset I) × Finset T × Finset I) =>  isColorful c x.2.1 x.2.2) (doubleCountingSet c i)).card
:= by
  let s := doubleCountingSet c i
  have cardeq' :=
    (Finset.card_filter_add_card_filter_not (s := s)
      (fun x => isOutsideDoor x.1.1 x.1.2)).symm
  have cardeq :=
    (Finset.card_filter_add_card_filter_not (s := s)
      (fun x => isColorful c x.2.1 x.2.2)).symm
  apply odd_of_odd_add_even_eq_add_even (odd_card_filter_isOutsideDoor c i)
    (even_card_filter_not_isOutsideDoor c i) (even_card_filter_not_isColorful c i)
  rw [<-cardeq',<-cardeq]

variable [Inhabited I]

theorem Scarf : (IST.colorful c).Nonempty := by
  have cardpos := Odd.pos $ odd_card_filter_isColorful c default
  replace nonempty:= Finset.card_pos.1 cardpos
  obtain ⟨x,hx⟩ := nonempty
  replace hx := (Finset.mem_filter.1 hx).2
  use x.2
  simp only [mem_filter, mem_univ, hx, and_self]


end Scarf

end IndexedLOrder
