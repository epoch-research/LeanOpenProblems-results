import Submission.EvenTerminalEquality

/-! Nonroot cycle vertices cannot split between two normal
components when the optimized cycle has at least four vertices. -/
namespace Erdos583EvenTwoComponentShapeDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion Erdos583Work.MemberComponents
open Erdos583UnifiedMinimalDefectDevelopment Erdos583EvenTerminalEqualityDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma inter_insert_count {V : Type*} [Finite V] (S K : Set V) (x : V) (hx : x ∉ K) :
    (S ∩ insert x K).ncard=(S ∩ K).ncard+(if x ∈ S then 1 else 0) := by
  by_cases hxs : x ∈ S
  · have he : S ∩ insert x K=insert x (S ∩ K) := by
      ext z
      simp only [Set.mem_inter_iff,Set.mem_insert_iff]
      constructor
      · rintro ⟨hz,rfl|hzK⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hz,hzK⟩
      · rintro (rfl|⟨hz,hzK⟩)
        · exact ⟨hxs,Or.inl rfl⟩
        · exact ⟨hz,Or.inr hzK⟩
    rw [he,Set.ncard_insert_of_notMem (fun h ↦ hx h.2),if_pos hxs]
  · have he : S ∩ insert x K=S ∩ K := by
      ext z
      simp only [Set.mem_inter_iff,Set.mem_insert_iff]
      constructor
      · rintro ⟨hz,rfl|hzK⟩
        · exact (hxs hz).elim
        · exact ⟨hz,hzK⟩
      · rintro ⟨hz,hzK⟩
        exact ⟨hz,Or.inr hzK⟩
    rw [he,if_neg hxs,Nat.add_zero]

lemma equal_insert_inter_membership {V : Type*} [Finite V] (S K : Set V) {x y : V}
    (hx : x ∉ K) (hy : y ∉ K)
    (he : (S ∩ insert x K).ncard=(S ∩ insert y K).ncard) : x ∈ S ↔ y ∈ S := by
  rw [inter_insert_count S K x hx,inter_insert_count S K y hy] at he
  by_cases hxs : x ∈ S <;> by_cases hys : y ∈ S <;> simp_all

variable (F : MinimalFailure) (D : OptimizedDefect F.graph)

lemma finish_not_on_cycle : D.rep.finish ∉ D.rep.cycle.toSubgraph.verts := by
  intro hf
  have he := D.rep.inter D.rep.finish (D.rep.cycle.mem_verts_toSubgraph.mp hf) D.rep.tail.end_mem_support
  exact (ContiguousRegion.path_ends_ne D.rep.tail D.rep.isPath (tail_not_nil F D)) he.symm

lemma long_cycle_normal_support (hlen : 4 ≤ D.rep.cycle.length) {x : Fin F.order}
    (hx : x ∈ D.rep.cycle.toSubgraph.verts) (hxr : x ≠ D.root) :
    x ∈ (selectedGraph D.family (Finset.univ.erase D.rep.index)).support := by
  have hroot : 3 ≤ Nat.card (F.graph.neighborSet D.root) := by
    have hd := FreeTailGroups.open_rooted_member_degree D.family D.root D.rep (tail_not_nil F D)
    have hh := Set.ncard_le_ncard (show (D.family.walk D.rep.index).toSubgraph.neighborSet D.root ⊆
      F.graph.neighborSet D.root from fun _ h ↦ (D.family.walk D.rep.index).toSubgraph.adj_sub h)
    rwa [hd,←Nat.card_coe_set_eq] at hh
  have hstructure := FreeCycleChoice.free_cycle_minimum_structure F.smaller F.connected F.failure
    D.family D.score D.root D.rep hroot (fun W M hs ↦ D.cycle_minimum W D.root M hs)
  have hd := (hstructure.resolve_left (by omega)) x (D.rep.cycle.mem_verts_toSubgraph.mp hx)
  by_contra hn
  have hs : x ∈ F.graph.support := by
    apply F.graph.mem_support.mpr
    apply (Set.ncard_pos (Set.toFinite (F.graph.neighborSet x))).mp
    rw [←Nat.card_coe_set_eq]
    omega
  have hinc := NormalRemainder.missing_incidence D.family D.root D.rep D.score D.maximum hs hn
  rw [if_neg hxr.symm] at hinc
  omega

lemma long_cycle_missing_terminals (hlen : 4 ≤ D.rep.cycle.length) :
    (selectedGraph D.family (Finset.univ.erase D.rep.index)).supportᶜ ⊆ {D.root,D.rep.finish} := by
  intro x hx
  rcases NormalRemainder.missing_on_cycle_or_finish F.smaller F.connected F.failure D.family
      D.root D.rep D.score D.maximum (fun W M hs _ hMC ↦ D.tail_minimum W M hs hMC) hx with hxC|hxf
  · by_cases hxr : x=D.root
    · exact Or.inl hxr
    · exact (hx (long_cycle_normal_support F D hlen (D.rep.cycle.mem_verts_toSubgraph.mpr hxC) hxr)).elim
  · exact Or.inr hxf

lemma cycle_terminal_data {x z : Fin F.order}
    (hx : x ∈ D.rep.cycle.toSubgraph.verts) (hz : z ∈ D.rep.cycle.toSubgraph.verts)
    (hxr : x ≠ D.root) (hzr : z ≠ D.root) (hxz : x ≠ z) :
    let K : Set (Fin F.order) := insert x {D.root,z,D.rep.finish}
    D.root ∈ K ∧ D.rep.finish ∈ K ∧
      3 ≤ (D.rep.cycle.toSubgraph.verts ∩ K).ncard ∧ K.ncard ≤ 4 := by
  let K : Set (Fin F.order) := insert x {D.root,z,D.rep.finish}
  have hsub : ({x,D.root,z} : Set (Fin F.order)) ⊆ D.rep.cycle.toSubgraph.verts ∩ K := by
    rintro v (rfl|rfl|rfl)
    · exact ⟨hx,by simp [K]⟩
    · exact ⟨D.rep.cycle.start_mem_verts_toSubgraph,by simp [K]⟩
    · exact ⟨hz,by simp [K]⟩
  have hthree := Set.ncard_le_ncard hsub
  have hcard1 := Set.ncard_insert_le x ({D.root,z,D.rep.finish} : Set (Fin F.order))
  have hcard2 := Set.ncard_insert_le D.root ({z,D.rep.finish} : Set (Fin F.order))
  have hcard3 := Set.ncard_insert_le z ({D.rep.finish} : Set (Fin F.order))
  simp only [Set.ncard_singleton] at hcard3
  refine ⟨by simp,by simp,?_,by change K.ncard ≤ 4; dsimp only [K]; omega⟩
  simpa [hxr,hxz,hzr.symm] using hthree

lemma third_nonroot_cycle_vertex (hlen : 4 ≤ D.rep.cycle.length) {x y : Fin F.order} :
    ∃ z ∈ D.rep.cycle.toSubgraph.verts, z ≠ D.root ∧ z ≠ x ∧ z ≠ y := by
  by_contra hn
  have hsub : D.rep.cycle.toSubgraph.verts ⊆ ({D.root,x,y} : Set (Fin F.order)) := by
    intro z hz
    by_cases hzr : z=D.root
    · exact Or.inl hzr
    by_cases hzx : z=x
    · exact Or.inr (Or.inl hzx)
    · exact Or.inr (Or.inr (by by_contra hzy; exact hn ⟨z,hz,hzr,hzx,hzy⟩))
  have hb := Set.ncard_le_ncard hsub
  rw [Walk.verts_toSubgraph,cycle_support_ncard D.rep.isCycle] at hb
  have hb1 := Set.ncard_insert_le D.root ({x,y} : Set (Fin F.order))
  have hb2 := Set.ncard_insert_le x ({y} : Set (Fin F.order))
  simp only [Set.ncard_singleton] at hb2
  omega

lemma even_two_cycle_membership (he : Even F.order)
    (htwo : Nat.card (NormalComponent F D)=2)
    (hlen : 4 ≤ D.rep.cycle.length) (A : NormalComponent F D)
    {x y : Fin F.order} (hx : x ∈ D.rep.cycle.toSubgraph.verts) (hy : y ∈ D.rep.cycle.toSubgraph.verts)
    (hxr : x ≠ D.root) (hyr : y ≠ D.root) :
    x ∈ componentSupport F D A ↔ y ∈ componentSupport F D A := by
  obtain ⟨z,hz,hzr,hzx,hzy⟩ := third_nonroot_cycle_vertex F D hlen (x := x) (y := y)
  let K : Set (Fin F.order) := {D.root,z,D.rep.finish}
  have hxf : x ≠ D.rep.finish := fun h ↦ finish_not_on_cycle F D (h ▸ hx)
  have hyf : y ≠ D.rep.finish := fun h ↦ finish_not_on_cycle F D (h ▸ hy)
  have hxK : x ∉ K := by simp [K,hxr,hzx.symm,hxf]
  have hyK : y ∉ K := by simp [K,hyr,hzy.symm,hyf]
  obtain ⟨hxrK,hxfK,hxC,hxcard⟩ := cycle_terminal_data F D hx hz hxr hzr hzx.symm
  obtain ⟨hyrK,hyfK,hyC,hycard⟩ := cycle_terminal_data F D hy hz hyr hzr hzy.symm
  have heqx := even_two_component_terminal_exact F D he htwo (insert x K) hxrK hxfK hxC hxcard
    ((long_cycle_missing_terminals F D hlen).trans (by rintro v (rfl|rfl) <;> simp [K])) A
  have heqy := even_two_component_terminal_exact F D he htwo (insert y K) hyrK hyfK hyC hycard
    ((long_cycle_missing_terminals F D hlen).trans (by rintro v (rfl|rfl) <;> simp [K])) A
  exact equal_insert_inter_membership (componentSupport F D A) K hxK hyK (heqx.symm.trans heqy)

lemma even_two_cycle_all_or_none (he : Even F.order)
    (htwo : Nat.card (NormalComponent F D)=2)
    (hlen : 4 ≤ D.rep.cycle.length) (A : NormalComponent F D) :
    (D.rep.cycle.toSubgraph.verts \ {D.root}) ⊆ componentSupport F D A ∨
      Disjoint (D.rep.cycle.toSubgraph.verts \ {D.root}) (componentSupport F D A) := by
  by_cases hh : ((D.rep.cycle.toSubgraph.verts \ {D.root}) ∩ componentSupport F D A).Nonempty
  · obtain ⟨x,⟨hx,hxr⟩,hxA⟩ := hh
    refine Or.inl ?_
    rintro y ⟨hy,hyr⟩
    exact (even_two_cycle_membership F D he htwo hlen A hx hy hxr hyr).mp hxA
  · exact Or.inr (Set.disjoint_left.mpr (fun x hx hxA ↦ hh ⟨x,hx,hxA⟩))

lemma even_two_cycle_component (he : Even F.order)
    (htwo : Nat.card (NormalComponent F D)=2)
    (hlen : 4 ≤ D.rep.cycle.length) :
    ∃ A : NormalComponent F D, (D.rep.cycle.toSubgraph.verts \ {D.root}) ⊆ componentSupport F D A ∧
      ∀ B : NormalComponent F D, B ≠ A →
        Disjoint (D.rep.cycle.toSubgraph.verts \ {D.root}) (componentSupport F D B) := by
  let x := D.rep.cycle.snd
  have hx : x ∈ D.rep.cycle.toSubgraph.verts :=
    D.rep.cycle.mem_verts_toSubgraph.mpr (D.rep.cycle.getVert_mem_support 1)
  have hxr : x ≠ D.root := (D.rep.cycle.toSubgraph_adj_snd D.rep.isCycle.not_nil).ne.symm
  have hxN : x ∈ (selectedGraph D.family (Finset.univ.erase D.rep.index)).support :=
    long_cycle_normal_support F D hlen hx hxr
  rw [←component_support_union] at hxN
  obtain ⟨A,hxA⟩ := Set.mem_iUnion.mp hxN
  have hsub : (D.rep.cycle.toSubgraph.verts \ {D.root}) ⊆ componentSupport F D A := by
    rintro y ⟨hy,hyr⟩
    exact (even_two_cycle_membership F D he htwo hlen A hx hy hxr hyr).mp hxA
  refine ⟨A,hsub,?_⟩
  intro B hBA
  exact (component_support_disjoint D.family D.rep.index hBA.symm).mono_left hsub


lemma even_component_avoiding_cycle_terminal_bound (he : Even F.order) (A : NormalComponent F D)
    (havoid : Disjoint (D.rep.cycle.toSubgraph.verts \ {D.root}) (componentSupport F D A)) :
    surplus F D A+1 ≤ (componentSupport F D A ∩ {D.root,D.rep.finish}).ncard := by
  let x := D.rep.cycle.snd
  let z := D.rep.cycle.penultimate
  have hx : x ∈ D.rep.cycle.toSubgraph.verts :=
    D.rep.cycle.mem_verts_toSubgraph.mpr (D.rep.cycle.getVert_mem_support 1)
  have hz : z ∈ D.rep.cycle.toSubgraph.verts :=
    D.rep.cycle.mem_verts_toSubgraph.mpr (D.rep.cycle.getVert_mem_support (D.rep.cycle.length-1))
  have hxr : x ≠ D.root := (D.rep.cycle.toSubgraph_adj_snd D.rep.isCycle.not_nil).ne.symm
  have hzr : z ≠ D.root := (D.rep.cycle.toSubgraph_adj_penultimate D.rep.isCycle.not_nil).ne
  have hxz : x ≠ z := D.rep.isCycle.snd_ne_penultimate
  obtain ⟨hr,hf,hC,_⟩ := cycle_terminal_data F D hx hz hxr hzr hxz
  have hb := even_component_terminal_surplus F D he (insert x {D.root,z,D.rep.finish}) hr hf hC A
  have hxA : x ∉ componentSupport F D A := fun hh ↦ Set.disjoint_left.mp havoid ⟨hx,hxr⟩ hh
  have hzA : z ∉ componentSupport F D A := fun hh ↦ Set.disjoint_left.mp havoid ⟨hz,hzr⟩ hh
  have heq : componentSupport F D A ∩ insert x {D.root,z,D.rep.finish}=
      componentSupport F D A ∩ {D.root,D.rep.finish} := by
    ext v
    constructor
    · rintro ⟨hv,rfl|rfl|rfl|rfl⟩
      · exact (hxA hv).elim
      · exact ⟨hv,Or.inl rfl⟩
      · exact (hzA hv).elim
      · exact ⟨hv,Or.inr rfl⟩
    · rintro ⟨hv,rfl|rfl⟩
      · exact ⟨hv,Or.inr (Or.inl rfl)⟩
      · exact ⟨hv,Or.inr (Or.inr (Or.inr rfl))⟩
  rwa [heq] at hb

lemma even_component_avoiding_cycle_terminals (he : Even F.order) (A : NormalComponent F D)
    (havoid : Disjoint (D.rep.cycle.toSubgraph.verts \ {D.root}) (componentSupport F D A)) :
    surplus F D A ≤ 1 ∧ (D.root ∈ componentSupport F D A ∨ D.rep.finish ∈ componentSupport F D A) := by
  have hb := even_component_avoiding_cycle_terminal_bound F D he A havoid
  have hi : (componentSupport F D A ∩ {D.root,D.rep.finish}).ncard ≤ 2 := by
    have hh := Set.ncard_le_ncard (Set.inter_subset_right (s := componentSupport F D A)
      (t := ({D.root,D.rep.finish} : Set (Fin F.order))))
    have hh' := Set.ncard_insert_le D.root ({D.rep.finish} : Set (Fin F.order))
    simp only [Set.ncard_singleton] at hh'
    omega
  have hp : 0 < (componentSupport F D A ∩ {D.root,D.rep.finish}).ncard := by omega
  obtain ⟨v,hv,hvr|hvf⟩ := (Set.ncard_pos (Set.toFinite _)).mp hp
  · exact ⟨by omega,Or.inl (hvr ▸ hv)⟩
  · exact ⟨by omega,Or.inr (hvf ▸ hv)⟩

lemma even_two_cycle_component_misses_terminal (he : Even F.order)
    (htwo : Nat.card (NormalComponent F D)=2)
    (hlen : 4 ≤ D.rep.cycle.length) :
    ∃ A : NormalComponent F D, (D.rep.cycle.toSubgraph.verts \ {D.root}) ⊆ componentSupport F D A ∧
      ¬(D.root ∈ componentSupport F D A ∧ D.rep.finish ∈ componentSupport F D A) ∧
      ∀ B : NormalComponent F D, B ≠ A → surplus F D B ≤ 1 ∧
        (D.root ∈ componentSupport F D B ∨ D.rep.finish ∈ componentSupport F D B) := by
  obtain ⟨A,hsub,hothers⟩ := even_two_cycle_component F D he htwo hlen
  have hotherterm (B : NormalComponent F D) (hBA : B ≠ A) :=
    even_component_avoiding_cycle_terminals F D he B (hothers B hBA)
  refine ⟨A,hsub,?_,hotherterm⟩
  rintro ⟨hr,hf⟩
  haveI : Nontrivial (NormalComponent F D) := Fintype.one_lt_card_iff_nontrivial.mp (by
    simpa only [←Nat.card_eq_fintype_card,htwo] using (show 1 < (2 : ℕ) by omega))
  obtain ⟨B,hBA⟩ := exists_ne A
  have hd := component_support_disjoint D.family D.rep.index hBA
  rcases (hotherterm B hBA).2 with hBr|hBf
  · exact Set.disjoint_left.mp hd hBr hr
  · exact Set.disjoint_left.mp hd hBf hf


lemma even_off_cycle_missing_terminal_zero (he : Even F.order) (A : NormalComponent F D)
    (havoid : Disjoint (D.rep.cycle.toSubgraph.verts \ {D.root}) (componentSupport F D A))
    (hmiss : D.root ∉ componentSupport F D A ∨ D.rep.finish ∉ componentSupport F D A) :
    surplus F D A=0 := by
  have hb := even_component_avoiding_cycle_terminal_bound F D he A havoid
  have hcard : (componentSupport F D A ∩ {D.root,D.rep.finish}).ncard ≤ 1 := by
    rcases hmiss with hr|hf
    · have hh := Set.ncard_le_ncard (show componentSupport F D A ∩ {D.root,D.rep.finish} ⊆
          ({D.rep.finish} : Set (Fin F.order)) from by
        rintro x ⟨hx,rfl|rfl⟩
        · exact (hr hx).elim
        · rfl)
      simpa only [Set.ncard_singleton] using hh
    · have hh := Set.ncard_le_ncard (show componentSupport F D A ∩ {D.root,D.rep.finish} ⊆
          ({D.root} : Set (Fin F.order)) from by
        rintro x ⟨hx,rfl|rfl⟩
        · rfl
        · exact (hf hx).elim)
      simpa only [Set.ncard_singleton] using hh
  omega

lemma zero_component_at_least_half (A : NormalComponent F D) (hzero : surplus F D A=0) :
    F.order ≤ 2*(componentSupport F D A).ncard :=
  Erdos583FreeTailAbsorptionDevelopment.zero_component_large F.smaller F.connected F.failure
    D.family D.score D.root D.rep D.tail_minimum A hzero

lemma even_two_cycle_component_at_most_half (he : Even F.order)
    (htwo : Nat.card (NormalComponent F D)=2) (A : NormalComponent F D)
    (hC : (D.rep.cycle.toSubgraph.verts \ {D.root}) ⊆ componentSupport F D A)
    (hterminal : D.root ∈ componentSupport F D A ∨ D.rep.finish ∈ componentSupport F D A) :
    2*(componentSupport F D A).ncard ≤ F.order := by
  haveI : Nontrivial (NormalComponent F D) := Fintype.one_lt_card_iff_nontrivial.mp (by
    simpa only [←Nat.card_eq_fintype_card,htwo] using (show 1 < (2 : ℕ) by omega))
  obtain ⟨B,hBA⟩ := exists_ne A
  have hd := component_support_disjoint D.family D.rep.index hBA
  have havoid : Disjoint (D.rep.cycle.toSubgraph.verts \ {D.root}) (componentSupport F D B) :=
    hd.symm.mono_left hC
  have hmiss : D.root ∉ componentSupport F D B ∨ D.rep.finish ∉ componentSupport F D B := by
    rcases hterminal with hr|hf
    · exact Or.inl (fun hB ↦ Set.disjoint_left.mp hd hB hr)
    · exact Or.inr (fun hB ↦ Set.disjoint_left.mp hd hB hf)
  have hlarge := zero_component_at_least_half F D B (even_off_cycle_missing_terminal_zero F D he B havoid hmiss)
  have hsum := Set.ncard_le_card (componentSupport F D B ∪ componentSupport F D A)
  rw [Set.ncard_union_eq hd,Nat.card_fin] at hsum
  simp only [componentSupport] at *
  omega

end Erdos583EvenTwoComponentShapeDevelopment
