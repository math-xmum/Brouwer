import Mathlib



open Classical Finset

noncomputable section

namespace PathComponents

/-- A graph has degree at most $2$ at each vertex. -/
def DegreeAtMostTwo {α : Type*} [Fintype α] (G : SimpleGraph α) : Prop :=
  ∀ v, G.degree v ≤ 2

/-- A connected component is represented by a Mathlib graph path. -/
def ComponentHasSpanningPath {α : Type*} [Fintype α]
    (G : SimpleGraph α) (component : G.ConnectedComponent) : Prop :=
  ∃ (u v : α) (p : G.Walk u v),
    p.IsPath ∧ {x : α | x ∈ p.support} = component.supp

/-- A connected component is represented by a Mathlib graph cycle. -/
def ComponentHasSpanningCycle {α : Type*} [Fintype α]
    (G : SimpleGraph α) (component : G.ConnectedComponent) : Prop :=
  ∃ (u : α) (p : G.Walk u u),
    p.IsCycle ∧ {x : α | x ∈ p.support} = component.supp

/-- Every component has a spanning path or a spanning cycle. -/
def ComponentsHaveSpanningPathsOrCycles {α : Type*} [Fintype α]
    (G : SimpleGraph α) : Prop :=
  ∀ component : G.ConnectedComponent,
    ComponentHasSpanningPath G component ∨ ComponentHasSpanningCycle G component

theorem exists_maximal_component_path_of_degree_le_two
    {α : Type*} [Fintype α] (G : SimpleGraph α)
    (_hdeg : DegreeAtMostTwo G) (component : G.ConnectedComponent) :
    ∃ (u v : α) (p : G.Walk u v),
      p.IsPath ∧
        {x : α | x ∈ p.support} ⊆ component.supp ∧
        ∀ (u' v' : α) (p' : G.Walk u' v'),
          p'.IsPath →
            {x : α | x ∈ p'.support} ⊆ component.supp →
              p'.length ≤ p.length := by
  classical
  let lengths : Set ℕ :=
    {n | ∃ (u v : α) (p : G.Walk u v),
      p.IsPath ∧ {x : α | x ∈ p.support} ⊆ component.supp ∧ p.length = n}
  have hfinite : lengths.Finite := by
    apply Set.Finite.subset (Set.finite_le_nat (Fintype.card α))
    intro n hn
    rcases hn with ⟨u, v, p, hp, _hsub, rfl⟩
    exact Nat.le_of_lt (SimpleGraph.Walk.IsPath.length_lt hp)
  obtain ⟨x, hxcomp⟩ := component.nonempty_supp
  have hnonempty : (0 : ℕ) ∈ lengths := by
    refine ⟨x, x, SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, ?_, rfl⟩
    intro y hy
    simp at hy
    rw [hy]
    exact hxcomp
  obtain ⟨n, ⟨hn_mem, hn_max⟩⟩ := hfinite.exists_maximal ⟨0, hnonempty⟩
  rcases hn_mem with ⟨u, v, p, hp, hp_sub, hp_len⟩
  refine ⟨u, v, p, hp, hp_sub, ?_⟩
  intro u' v' p' hp' hp'_sub
  have hp'_len_mem : p'.length ∈ lengths :=
    ⟨u', v', p', hp', hp'_sub, rfl⟩
  have := hn_max hp'_len_mem
  omega

/--
Generic graph-theoretic step $2\mathrm{a}$: in a graph of degree at most $2$, a maximal
component path has no neighbor outside its support.  This is the point that
rules out $T$-shaped components.
-/
theorem maximal_component_path_no_escape_of_degree_le_two
    {α : Type*} [Fintype α] (G : SimpleGraph α)
    (hdeg : DegreeAtMostTwo G)
    {component : G.ConnectedComponent} {u v : α} {p : G.Walk u v}
    (hp : p.IsPath)
    (hp_sub : {x : α | x ∈ p.support} ⊆ component.supp)
    (hmax :
      ∀ (u' v' : α) (p' : G.Walk u' v'),
        p'.IsPath →
          {x : α | x ∈ p'.support} ⊆ component.supp →
            p'.length ≤ p.length)
    {x y : α}
    (hx : x ∈ p.support)
    (hxy : G.Adj x y)
    (hycomp : y ∈ component.supp) :
    y ∈ p.support := by
  by_contra hyNot
  by_cases hxu : x = u
  · subst hxu
    let p' : G.Walk y v := SimpleGraph.Walk.cons hxy.symm p
    have hp' : p'.IsPath := by
      change (SimpleGraph.Walk.cons hxy.symm p).IsPath
      exact (SimpleGraph.Walk.cons_isPath_iff hxy.symm p).2 ⟨hp, hyNot⟩
    have hp'_sub : {z : α | z ∈ p'.support} ⊆ component.supp := by
      intro z hz
      simp [p', SimpleGraph.Walk.support_cons] at hz
      rcases hz with rfl | hz
      · exact hycomp
      · exact hp_sub hz
    have hle := hmax y v p' hp' hp'_sub
    simp [p'] at hle
  by_cases hxv : x = v
  · subst hxv
    let p' : G.Walk u y := p.concat hxy
    have hp' : p'.IsPath := by
      change (p.concat hxy).IsPath
      exact (SimpleGraph.Walk.concat_isPath_iff hxy).2 ⟨hp, hyNot⟩
    have hp'_sub : {z : α | z ∈ p'.support} ⊆ component.supp := by
      intro z hz
      simp [p'] at hz
      rcases hz with hz | rfl
      · exact hp_sub hz
      · exact hycomp
    have hle := hmax u y p' hp' hp'_sub
    simp [p'] at hle
  obtain ⟨q, r, hqPath, hrPath, hqr⟩ := (SimpleGraph.Walk.IsPath.mem_support_iff_exists_append hp).1 hx
  have hqNonNil : ¬ q.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    exact fun hux => hxu hux.symm
  have hrNonNil : ¬ r.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    exact hxv
  let a : α := q.penultimate
  let b : α := r.snd
  have haAdj : G.Adj x a := (q.adj_penultimate hqNonNil).symm
  have hbAdj : G.Adj x b := r.adj_snd hrNonNil
  have haQ : a ∈ q.support := by
    exact q.getVert_mem_support (q.length - 1)
  have hbR : b ∈ r.support := by
    exact r.getVert_mem_support 1
  have hpqr : (q.append r).IsPath := by
    rwa [← hqr]
  have hb_ne_x : b ≠ x := hbAdj.ne.symm
  have hab : a ≠ b :=
    SimpleGraph.Walk.IsPath.ne_of_mem_support_of_append hpqr hb_ne_x haQ hbR
  have haP : a ∈ p.support := by
    rw [hqr, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl haQ
  have hbP : b ∈ p.support := by
    rw [hqr, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr hbR
  have hay : a ≠ y := fun h => hyNot (h ▸ haP)
  have hby : b ≠ y := fun h => hyNot (h ▸ hbP)
  have hTripleSubset : ({a, b, y} : Finset α) ⊆ (G.neighborFinset x) := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz
    rw [SimpleGraph.mem_neighborFinset]
    rcases hz with rfl | rfl | rfl
    · exact haAdj
    · exact hbAdj
    · exact hxy
  have hTripleCard : ({a, b, y} : Finset α).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨a, b, y, hab, hay, hby, rfl⟩
  have hThreeLe : 3 ≤ G.degree x := by
    rw [SimpleGraph.degree, ← hTripleCard]
    exact Finset.card_le_card hTripleSubset
  have hTwo := hdeg x
  omega

/--
Generic graph-theoretic step $2\mathrm{b}$: if a component path has no edge escaping its
support inside the component, then its support is the whole component.
-/
theorem component_path_support_eq_component_of_no_escape
    {α : Type*} [Fintype α] (G : SimpleGraph α)
    {component : G.ConnectedComponent} {u v : α} {p : G.Walk u v}
    (hp_sub : {x : α | x ∈ p.support} ⊆ component.supp)
    (hend :
      ∀ ⦃x y : α⦄,
        x ∈ p.support →
          G.Adj x y →
            y ∈ component.supp →
              y ∈ p.support) :
    {x : α | x ∈ p.support} = component.supp := by
  ext z
  constructor
  · intro hz
    exact hp_sub hz
  · intro hzcomp
    by_contra hzNot
    have huSupport : u ∈ p.support := p.start_mem_support
    have hucomp : u ∈ component.supp := hp_sub huSupport
    have hReach : G.Reachable u z := by
      apply SimpleGraph.ConnectedComponent.exact
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hucomp hzcomp
      exact hucomp.trans hzcomp.symm
    rcases hReach with ⟨q⟩
    obtain ⟨d, hdq, hdfst, hdsnd⟩ :=
      q.exists_boundary_dart {x : α | x ∈ p.support} huSupport hzNot
    have hdfstComp : d.fst ∈ component.supp := hp_sub hdfst
    have hdsndComp : d.snd ∈ component.supp := by
      exact (SimpleGraph.ConnectedComponent.mem_supp_congr_adj component d.adj).1 hdfstComp
    have hEscape : d.snd ∈ p.support := hend hdfst d.adj hdsndComp
    exact hdsnd hEscape

/-- Generic graph-theoretic step $3$: if a maximal component path in a degree-at-most-$2$
graph has a closing edge not already used by the path, then the component
is a cycle.  The extra edge condition excludes the $2$-vertex path case. -/
theorem component_cycle_of_maximal_path_closes
    {α : Type*} [Fintype α] (G : SimpleGraph α)
    {component : G.ConnectedComponent} {u v : α} {p : G.Walk u v}
    (hp : p.IsPath)
    (hsupp : {x : α | x ∈ p.support} = component.supp)
    (hclose : G.Adj v u)
    (hnew : s(v, u) ∉ p.edges) :
    ComponentHasSpanningCycle G component := by
  refine ⟨v, SimpleGraph.Walk.cons hclose p, ?_, ?_⟩
  · exact (SimpleGraph.Walk.cons_isCycle_iff p hclose).2 ⟨hp, hnew⟩
  · rw [← hsupp]
    ext x
    constructor
    · intro hx
      simp [SimpleGraph.Walk.support_cons] at hx
      rcases hx with rfl | hx
      · exact p.end_mem_support
      · exact hx
    · intro hx
      simp [SimpleGraph.Walk.support_cons]
      exact Or.inr hx

/-- A path whose support is exactly a component represents that component as a path. -/
theorem component_path_of_support_eq_component
    {α : Type*} [Fintype α] (G : SimpleGraph α)
    {component : G.ConnectedComponent} {u v : α} {p : G.Walk u v}
    (hp : p.IsPath)
    (hsupp : {x : α | x ∈ p.support} = component.supp) :
    ComponentHasSpanningPath G component := by
  exact ⟨u, v, p, hp, hsupp⟩

/--
Every connected component of a finite graph whose vertices all have degree
at most $2$ has a spanning path or a spanning cycle.
-/
theorem components_have_spanning_paths_or_cycles_of_degree_le_two
    {α : Type*} [Fintype α] (G : SimpleGraph α)
    (hdeg : DegreeAtMostTwo G) :
    ComponentsHaveSpanningPathsOrCycles G := by
  intro component
  obtain ⟨u, v, p, hp, hp_sub, hmax⟩ :=
    exists_maximal_component_path_of_degree_le_two G hdeg component
  have hNoEscape :
      ∀ ⦃x y : α⦄,
        x ∈ p.support →
          G.Adj x y →
            y ∈ component.supp →
              y ∈ p.support := by
    intro x y hx hxy hycomp
    exact maximal_component_path_no_escape_of_degree_le_two G hdeg hp hp_sub hmax hx hxy hycomp
  have hsupp : {x : α | x ∈ p.support} = component.supp :=
    component_path_support_eq_component_of_no_escape G hp_sub hNoEscape
  by_cases hcycle : G.Adj v u ∧ s(v, u) ∉ p.edges
  · exact Or.inr (component_cycle_of_maximal_path_closes G hp hsupp hcycle.1 hcycle.2)
  · exact Or.inl (component_path_of_support_eq_component G hp hsupp)

def reachableComponent {α : Type*} (G : SimpleGraph α) (v₀ : α) :
    SimpleGraph {v : α // G.Reachable v₀ v} where
  Adj a b := G.Adj a.1 b.1
  symm := ⟨fun a b h => G.symm.symm a.1 b.1 h⟩
  loopless := ⟨fun a h => G.loopless.1 a.1 h⟩

lemma reachableComponent_degree
    {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) (v₀ : α)
    (x : {v : α // G.Reachable v₀ v}) :
    (reachableComponent G v₀).degree x = G.degree x.1 := by
  classical
  let H : SimpleGraph {v : α // G.Reachable v₀ v} := reachableComponent G v₀
  change H.degree x = G.degree x.1
  have hImage :
      (H.neighborFinset x).image (fun y : {v : α // G.Reachable v₀ v} => y.1) =
        G.neighborFinset x.1 := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
      exact (SimpleGraph.mem_neighborFinset G x.1 z.1).2
        ((SimpleGraph.mem_neighborFinset H x z).1 hz)
    · intro hy
      have hAdj : G.Adj x.1 y := (SimpleGraph.mem_neighborFinset G x.1 y).1 hy
      have hReachY : G.Reachable v₀ y := by
        rcases x.2 with ⟨p⟩
        exact ⟨p.concat hAdj⟩
      exact Finset.mem_image.mpr
        ⟨⟨y, hReachY⟩, (SimpleGraph.mem_neighborFinset H x ⟨y, hReachY⟩).2 hAdj, rfl⟩
  calc
    H.degree x = (H.neighborFinset x).card := rfl
    _ = ((H.neighborFinset x).image (fun y : {v : α // G.Reachable v₀ v} => y.1)).card := by
      rw [Finset.card_image_of_injOn]
      intro a _ b _ h
      exact Subtype.ext h
    _ = (G.neighborFinset x.1).card := by rw [hImage]
    _ = G.degree x.1 := rfl

end PathComponents
