import Submission.NormalTerminalBudget

/-! Four terminals can also cover the missing normal vertices. This removes
the spanning hypothesis from the even-order two-component bound. -/
namespace Erdos583EvenNormalTerminalBudgetDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583Work.QuotaTrails Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion Erdos583Work.MemberComponents
open Erdos583NormalTerminalBudgetDevelopment Erdos583UnifiedMinimalDefectDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma four_terminals_at_cycle_vertex {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r) {w : V} (hw : w ∈ L.cycle.toSubgraph.verts) :
    ∃ K : Set V, r ∈ K ∧ L.finish ∈ K ∧ w ∈ K ∧ 3 ≤ (L.cycle.toSubgraph.verts ∩ K).ncard ∧ K.ncard ≤ 4 := by
  by_cases hwr : w=r
  · obtain ⟨K,hr,hf,hC,hK⟩ := four_lollipop_terminals T r L
    exact ⟨K,hr,hf,hwr ▸ hr,hC,hK⟩
  have hrw : r ≠ w := fun hh ↦ hwr hh.symm
  have hex : ∃ y ∈ L.cycle.toSubgraph.verts, y ≠ r ∧ y ≠ w := by
    by_contra hno
    have hsub : L.cycle.toSubgraph.verts ⊆ ({r,w} : Set V) := by
      intro y hy
      by_cases hyr : y=r
      · exact Or.inl hyr
      · exact Or.inr (by by_contra hyw; exact hno ⟨y,hy,hyr,hyw⟩)
    have hh := Set.ncard_le_ncard hsub
    rw [Walk.verts_toSubgraph,cycle_support_ncard L.isCycle,Set.ncard_pair hrw] at hh
    have hc := L.isCycle.three_le_length
    omega
  obtain ⟨y,hy,hyr,hyw⟩ := hex
  let K : Set V := {r,w,y,L.finish}
  have hsub : ({r,w,y} : Set V) ⊆ L.cycle.toSubgraph.verts ∩ K := by
    rintro z (rfl|rfl|rfl)
    · exact ⟨L.cycle.start_mem_verts_toSubgraph,by simp [K]⟩
    · exact ⟨hw,by simp [K]⟩
    · exact ⟨hy,by simp [K]⟩
  have hthree : 3 ≤ (L.cycle.toSubgraph.verts ∩ K).ncard := by
    have hh := Set.ncard_le_ncard hsub
    simpa [hrw,hyr.symm,hyw.symm] using hh
  have hc1 := Set.ncard_insert_le r ({w,y,L.finish} : Set V)
  have hc2 := Set.ncard_insert_le w ({y,L.finish} : Set V)
  have hc3 := Set.ncard_insert_le y ({L.finish} : Set V)
  simp only [Set.ncard_singleton] at hc3
  exact ⟨K,by simp [K],by simp [K],by simp [K],hthree,
    by change ({r,w,y,L.finish} : Set V).ncard ≤ 4; omega⟩

lemma normal_complement_at_most_one (F : MinimalFailure) (D : OptimizedDefect F.graph) :
    (selectedGraph D.family (Finset.univ.erase D.rep.index)).supportᶜ.ncard ≤ 1 := by
  have hd := FreeTailGroups.open_rooted_member_degree D.family D.root D.rep (tail_not_nil F D)
  have hb := Set.ncard_le_ncard (show (D.family.walk D.rep.index).toSubgraph.neighborSet D.root ⊆
    F.graph.neighborSet D.root from fun _ h ↦ (D.family.walk D.rep.index).toSubgraph.adj_sub h)
  rw [hd,←Nat.card_coe_set_eq] at hb
  exact FreeCycleChoice.free_cycle_tail_normal_complement F.smaller F.connected F.failure D.family D.score
    D.root D.rep hb (fun W M hWs ↦ D.cycle_minimum W D.root M hWs) D.tail_minimum

lemma four_terminals_cover_missing (F : MinimalFailure) (D : OptimizedDefect F.graph) :
    ∃ K : Set (Fin F.order), D.root ∈ K ∧ D.rep.finish ∈ K ∧
      3 ≤ (D.rep.cycle.toSubgraph.verts ∩ K).ncard ∧ K.ncard ≤ 4 ∧
      (selectedGraph D.family (Finset.univ.erase D.rep.index)).supportᶜ ⊆ K := by
  let N := (selectedGraph D.family (Finset.univ.erase D.rep.index)).support
  have hsub := Set.ncard_le_one_iff_subsingleton.mp (normal_complement_at_most_one F D)
  by_cases hex : Nᶜ.Nonempty
  · obtain ⟨w,hw⟩ := hex
    have hw' := NormalRemainder.missing_on_cycle_or_finish F.smaller F.connected F.failure
      D.family D.root D.rep D.score D.maximum (fun W M hWs _ hMC ↦ D.tail_minimum W M hWs hMC) hw
    rcases hw' with hwC|hwf
    · obtain ⟨K,hr,hf,hwK,hC,hK⟩ := four_terminals_at_cycle_vertex D.family D.root D.rep
        (D.rep.cycle.mem_verts_toSubgraph.mpr hwC)
      exact ⟨K,hr,hf,hC,hK,fun z hz ↦ (hsub hz hw).symm ▸ hwK⟩
    · obtain ⟨K,hr,hf,hC,hK⟩ := four_lollipop_terminals D.family D.root D.rep
      exact ⟨K,hr,hf,hC,hK,fun z hz ↦ ((hsub hz hw).trans hwf).symm ▸ hf⟩
  · obtain ⟨K,hr,hf,hC,hK⟩ := four_lollipop_terminals D.family D.root D.rep
    exact ⟨K,hr,hf,hC,hK,fun z hz ↦ (hex ⟨z,hz⟩).elim⟩

lemma terminal_intersections_sum_eq {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) (K : Set V) :
    (∑ A : (normalGraph T i).ConnectedComponent,
      ((selectedGraph T (componentMembers T i A)).support ∩ K).ncard) =
      ((selectedGraph T (Finset.univ.erase i)).support ∩ K).ncard := by
  have hdis : Pairwise (fun A B : (normalGraph T i).ConnectedComponent ↦
      Disjoint ((selectedGraph T (componentMembers T i A)).support ∩ K)
        ((selectedGraph T (componentMembers T i B)).support ∩ K)) := by
    intro A B hAB
    exact (component_support_disjoint T i hAB).mono Set.inter_subset_left Set.inter_subset_left
  have he := Set.ncard_iUnion_of_finite
    (fun A : (normalGraph T i).ConnectedComponent ↦ Set.toFinite ((selectedGraph T (componentMembers T i A)).support ∩ K)) hdis
  rw [finsum_eq_sum_of_fintype] at he
  rw [←he,←Set.iUnion_inter,component_support_union]

lemma even_normal_components_le_two (F : MinimalFailure) (D : OptimizedDefect F.graph) (ho : Even F.order) :
    Nat.card (normalGraph D.family D.rep.index).ConnectedComponent ≤ 2 := by
  obtain ⟨K,hr,hf,hC,hK,hmissing⟩ := four_terminals_cover_missing F D
  have hsum := Finset.sum_le_sum (fun A (_ : A ∈ (Finset.univ : Finset (normalGraph D.family D.rep.index).ConnectedComponent)) ↦
    component_terminal_budget F D K hr hf hC A)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    ←Finset.mul_sum,sum_component_support,sum_component_members,terminal_intersections_sum_eq] at hsum
  let N := (selectedGraph D.family (Finset.univ.erase D.rep.index)).support
  have hcover : N ∪ K=Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    by_cases hz : z ∈ N
    · exact Or.inl hz
    · exact Or.inr (hmissing hz)
  have hcount := Set.ncard_union_add_ncard_inter N K
  rw [hcover,Set.ncard_univ,Nat.card_fin] at hcount
  have hbudget : 2*budget F.order=F.order := by
    obtain ⟨q,hq⟩ := ho
    simp only [budget,ceil_half,Fintype.card_fin]
    omega
  have hpos : 1 ≤ budget F.order := by have hh := D.rep.index.isLt; omega
  change N.ncard+_+_ ≤ _+_+(N ∩ K).ncard at hsum
  rw [Nat.card_eq_fintype_card]
  rw [hbudget] at hsum
  have hminus := Nat.sub_add_cancel hpos
  nlinarith

end Erdos583EvenNormalTerminalBudgetDevelopment
