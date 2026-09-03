import Submission.LollipopFullRunCompression

/-! A terminal-count inequality for normal components. Four retained vertices
suffice for full lollipop compression. On odd order the inequality forces the
normal remainder of an optimized minimal failure to be connected. -/
namespace Erdos583NormalTerminalBudgetDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion Erdos583Work.MemberComponents
open Erdos583LollipopFullRunCompressionDevelopment
open Erdos583UnifiedMinimalDefectDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma component_terminal_budget (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (K : Set (Fin F.order)) (hr : D.root ∈ K) (hf : D.rep.finish ∈ K)
    (hC : 3 ≤ (D.rep.cycle.toSubgraph.verts ∩ K).ncard)
    (A : (normalGraph D.family D.rep.index).ConnectedComponent) :
    (selectedGraph D.family (componentMembers D.family D.rep.index A)).support.ncard+
        2*budget F.order+1 ≤ F.order+2*(componentMembers D.family D.rep.index A).card+
        ((selectedGraph D.family (componentMembers D.family D.rep.index A)).support ∩ K).ncard := by
  let B := componentMembers D.family D.rep.index A
  let S := (selectedGraph D.family B).support
  let R := S \ K
  have hp : 0 < B.card := (componentMembers_nonempty D.family D.rep.index A).card_pos
  have hsplit : (S ∩ K).ncard+R.ncard=S.ncard := Set.ncard_inter_add_ncard_diff_eq_ncard S K
  have hsum : R.ncard+Rᶜ.ncard=F.order := by simpa only [Nat.card_fin] using R.ncard_add_ncard_compl
  have hk : 2*budget F.order ≤ F.order+1 := by simp only [budget,ceil_half,Fintype.card_fin]; omega
  change S.ncard+2*budget F.order+1 ≤ F.order+2*B.card+(S ∩ K).ncard
  by_contra hn
  have hRp : 0 < R.ncard := by omega
  have hRn : R.Nonempty := (Set.ncard_pos (Set.toFinite _)).mp hRp
  have hout : 3 ≤ (D.rep.cycle.toSubgraph.verts \ R).ncard := hC.trans (Set.ncard_le_ncard (by
    rintro z ⟨hzC,hzK⟩
    exact ⟨hzC,fun hh ↦ hh.2 hzK⟩))
  apply no_compressible_normal_component F.smaller F.connected F.failure D.family D.score D.root D.rep
    (fun W M hWs _ ↦ D.cycle_minimum W D.root M hWs)
    (fun W M hWs _ hMC ↦ D.tail_minimum W M hWs hMC) A R Set.diff_subset hRn
    (fun hh ↦ hh.2 hr) (fun hh ↦ hh.2 hf) hout
  change B.card+⌈(Rᶜ.ncard : ℚ)/2⌉₊ ≤ budget F.order
  rw [ceil_half]
  omega

lemma terminal_intersections_sum_le {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) (K : Set V) :
    (∑ A : (normalGraph T i).ConnectedComponent,
      ((selectedGraph T (componentMembers T i A)).support ∩ K).ncard) ≤ K.ncard := by
  have hdis : Pairwise (fun A B : (normalGraph T i).ConnectedComponent ↦
      Disjoint ((selectedGraph T (componentMembers T i A)).support ∩ K)
        ((selectedGraph T (componentMembers T i B)).support ∩ K)) := by
    intro A B hAB
    exact (component_support_disjoint T i hAB).mono Set.inter_subset_left Set.inter_subset_left
  have he := Set.ncard_iUnion_of_finite
    (fun A : (normalGraph T i).ConnectedComponent ↦ Set.toFinite ((selectedGraph T (componentMembers T i A)).support ∩ K)) hdis
  rw [finsum_eq_sum_of_fintype] at he
  rw [←he]
  exact Set.ncard_le_ncard (by rintro z hz; obtain ⟨A,hA⟩ := Set.mem_iUnion.mp hz; exact hA.2)

lemma four_lollipop_terminals {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (L : RootedCycleRep T r) :
    ∃ K : Set V, r ∈ K ∧ L.finish ∈ K ∧ 3 ≤ (L.cycle.toSubgraph.verts ∩ K).ncard ∧ K.ncard ≤ 4 := by
  let x := L.cycle.getVert 1
  let y := L.cycle.getVert 2
  have hlen := L.isCycle.three_le_length
  have hrx : r ≠ x := by
    intro he
    have hh := (L.isCycle.getVert_endpoint_iff (show 1 ≤ L.cycle.length by omega)).mp he.symm
    omega
  have hry : r ≠ y := by
    intro he
    have hh := (L.isCycle.getVert_endpoint_iff (show 2 ≤ L.cycle.length by omega)).mp he.symm
    omega
  have hxy : x ≠ y := by
    intro he
    have hh := L.isCycle.getVert_injOn (show 1 ≤ 1 ∧ 1 ≤ L.cycle.length by omega)
      (show 1 ≤ 2 ∧ 2 ≤ L.cycle.length by omega) he
    omega
  let K : Set V := {r,x,y,L.finish}
  have hthree : 3 ≤ (L.cycle.toSubgraph.verts ∩ K).ncard := by
    have hsub : ({r,x,y} : Set V) ⊆ L.cycle.toSubgraph.verts ∩ K := by
      rintro z (rfl|rfl|rfl)
      · exact ⟨L.cycle.start_mem_verts_toSubgraph,by simp [K]⟩
      · exact ⟨L.cycle.mem_verts_toSubgraph.mpr (L.cycle.getVert_mem_support 1),by simp [K]⟩
      · exact ⟨L.cycle.mem_verts_toSubgraph.mpr (L.cycle.getVert_mem_support 2),by simp [K]⟩
    have hh := Set.ncard_le_ncard hsub
    simpa only [Set.ncard_insert_of_notMem (show r ∉ ({x,y} : Set V) by simp [hrx,hry]),
      Set.ncard_pair hxy] using hh
  have hc1 := Set.ncard_insert_le r ({x,y,L.finish} : Set V)
  have hc2 := Set.ncard_insert_le x ({y,L.finish} : Set V)
  have hc3 := Set.ncard_insert_le y ({L.finish} : Set V)
  simp only [Set.ncard_singleton] at hc3
  exact ⟨K,by simp [K],by simp [K],hthree,by change ({r,x,y,L.finish} : Set V).ncard ≤ 4; omega⟩

lemma odd_normal_components_le_one (F : MinimalFailure) (D : OptimizedDefect F.graph) (ho : Odd F.order) :
    Nat.card (normalGraph D.family D.rep.index).ConnectedComponent ≤ 1 := by
  obtain ⟨K,hr,hf,hC,hK⟩ := four_lollipop_terminals D.family D.root D.rep
  have hsum := Finset.sum_le_sum (fun A (_ : A ∈ (Finset.univ : Finset (normalGraph D.family D.rep.index).ConnectedComponent)) ↦
    component_terminal_budget F D K hr hf hC A)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    ←Finset.mul_sum,sum_component_support,sum_component_members] at hsum
  have hspan := TailEar.odd_normal_support_spanning F.smaller ho F.connected F.failure
    D.family D.root D.rep D.score D.maximum
  rw [hspan,Set.ncard_univ,Nat.card_fin] at hsum
  have hret := (terminal_intersections_sum_le D.family D.rep.index K).trans hK
  have hbudget : 2*budget F.order=F.order+1 := by
    obtain ⟨q,hq⟩ := ho
    simp only [budget,ceil_half,Fintype.card_fin]
    omega
  have hpos : 1 ≤ budget F.order := by have hh := D.rep.index.isLt; omega
  rw [Nat.card_eq_fintype_card]
  rw [hbudget] at hsum
  have hminus := Nat.sub_add_cancel hpos
  nlinarith

lemma odd_component_members (F : MinimalFailure) (D : OptimizedDefect F.graph) (ho : Odd F.order)
    (A : (normalGraph D.family D.rep.index).ConnectedComponent) :
    componentMembers D.family D.rep.index A=Finset.univ.erase D.rep.index := by
  haveI : Subsingleton (normalGraph D.family D.rep.index).ConnectedComponent :=
    (Fintype.card_le_one_iff_subsingleton).mp (by simpa only [Nat.card_eq_fintype_card] using odd_normal_components_le_one F D ho)
  ext j
  simp only [Finset.mem_erase,Finset.mem_univ,and_true]
  constructor
  · intro hj
    exact ((mem_componentMembers D.family D.rep.index j A).mp hj).1
  · intro hj
    exact (mem_componentMembers D.family D.rep.index j A).mpr ⟨hj,Subsingleton.elim _ _⟩

lemma odd_component_surplus_one (F : MinimalFailure) (D : OptimizedDefect F.graph) (ho : Odd F.order)
    (A : (normalGraph D.family D.rep.index).ConnectedComponent) :
    CycleComponentBudget.componentSurplus D.family D.rep.index A=1 := by
  unfold CycleComponentBudget.componentSurplus
  rw [odd_component_members F D ho A]
  have hspan := TailEar.odd_normal_support_spanning F.smaller ho F.connected F.failure
    D.family D.root D.rep D.score D.maximum
  rw [hspan,Set.ncard_univ,Nat.card_fin,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin]
  obtain ⟨q,hq⟩ := ho
  have hpos : 0 < F.order := by have := D.root.isLt; omega
  simp only [budget,ceil_half,Fintype.card_fin]
  omega

lemma odd_normal_remainder_connected (F : MinimalFailure) (D : OptimizedDefect F.graph) (ho : Odd F.order) :
    (selectedGraph D.family (Finset.univ.erase D.rep.index)).Connected := by
  have hspan := TailEar.odd_normal_support_spanning F.smaller ho F.connected F.failure
    D.family D.root D.rep D.score D.maximum
  obtain ⟨y,j,hj,_⟩ : D.root ∈ (selectedGraph D.family (Finset.univ.erase D.rep.index)).support := by
    rw [hspan]
    trivial
  let A := (normalGraph D.family D.rep.index).connectedComponentMk ⟨j,(Finset.mem_erase.mp hj).1⟩
  have hc := component_support_connected D.family D.rep.index A
  rw [odd_component_members F D ho A] at hc
  letI : Nonempty (Fin F.order) := ⟨D.root⟩
  exact ⟨fun x y ↦ hc x (hspan.symm ▸ Set.mem_univ x) y (hspan.symm ▸ Set.mem_univ y)⟩

lemma spanning_even_normal_components_le_two (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (ho : Even F.order)
    (hspan : (selectedGraph D.family (Finset.univ.erase D.rep.index)).support=Set.univ) :
    Nat.card (normalGraph D.family D.rep.index).ConnectedComponent ≤ 2 := by
  obtain ⟨K,hr,hf,hC,hK⟩ := four_lollipop_terminals D.family D.root D.rep
  have hsum := Finset.sum_le_sum (fun A (_ : A ∈ (Finset.univ : Finset (normalGraph D.family D.rep.index).ConnectedComponent)) ↦
    component_terminal_budget F D K hr hf hC A)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    ←Finset.mul_sum,sum_component_support,sum_component_members] at hsum
  rw [hspan,Set.ncard_univ,Nat.card_fin] at hsum
  have hret := (terminal_intersections_sum_le D.family D.rep.index K).trans hK
  have hbudget : 2*budget F.order=F.order := by
    obtain ⟨q,hq⟩ := ho
    simp only [budget,ceil_half,Fintype.card_fin]
    omega
  have hpos : 1 ≤ budget F.order := by have hh := D.rep.index.isLt; omega
  rw [Nat.card_eq_fintype_card]
  rw [hbudget] at hsum
  have hminus := Nat.sub_add_cancel hpos
  nlinarith

end Erdos583NormalTerminalBudgetDevelopment
