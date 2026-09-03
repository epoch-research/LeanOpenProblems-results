import Submission.RootedCycleNeighborClosure
import Submission.IndependentSuppression
import Submission.NormalComponentComplement

/-! A guarded suppression result for a normal component beside an arbitrary lollipop tail.
Avoidance of the tail and independence on the cycle are explicit hypotheses. -/
namespace Erdos583LollipopComponentSuppressionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.MemberComponents Erdos583Work.CycleEar Erdos583Work.BridgeGlue
open Erdos583IndependentSuppressionDevelopment Erdos583CycleNeighborClosureDevelopment
open Erdos583NormalComponentComplementDevelopment Erdos583RootedCycleNeighborClosureDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma independent_tail_avoiding_shortcuts {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (root : V) (L : RootedCycleRep T root)
    (hmin : ∀ W : TrailFamily G k, ∀ M : RootedCycleRep W root,
      W.score=T.score → (∀ z, W.quota z=T.quota z) → L.cycle.length ≤ M.cycle.length)
    (hlen : 4 < L.cycle.length) (A : (normalGraph T L.index).ConnectedComponent)
    (hTail : Disjoint L.tail.toSubgraph.verts (selectedGraph T (componentMembers T L.index A)).support)
    (hInd : ∀ x ∈ (selectedGraph T (componentMembers T L.index A)).support,
      ∀ y ∈ (selectedGraph T (componentMembers T L.index A)).support, ¬L.cycle.toSubgraph.Adj x y) :
    let S := (selectedGraph T (componentMembers T L.index A)).support
    let F := selectedGraph T (Finset.univ \ componentMembers T L.index A)
    let H := within F Sᶜ
    ∃ R : Finset V, ∃ a b : V → V,
      (R : Set V) ⊆ S ∧ (∀ r ∈ R, a r ∉ S) ∧ (∀ r ∈ R, b r ∉ S) ∧
      (∀ r ∈ R, a r ≠ b r) ∧ (∀ r ∈ R, ¬H.Adj (a r) (b r)) ∧
      (∀ r ∈ R, ∀ s ∈ R, s(a r,b r)=s(a s,b s) → r=s) ∧ F=H ⊔ spokes R a b := by
  let i := L.index
  let C := L.cycle
  have hC := L.isCycle
  change 4 < C.length at hlen
  let S := (selectedGraph T (componentMembers T i A)).support
  let F := selectedGraph T (Finset.univ \ componentMembers T i A)
  let H := within F Sᶜ
  let R := (C.toSubgraph.verts ∩ S).toFinset
  have hR (r : V) : r ∈ R ↔ r ∈ C.toSubgraph.verts ∧ r ∈ S := by simp only [R,Set.mem_toFinset,Set.mem_inter_iff]
  have hchoose (r : V) : ∃ a b, r ∈ R → a ≠ b ∧ C.toSubgraph.neighborSet r={a,b} := by
    by_cases hr : r ∈ R
    · obtain ⟨a,b,hab,hN⟩ := Set.ncard_eq_two.mp
        (hC.ncard_neighborSet_toSubgraph_eq_two (C.mem_verts_toSubgraph.mp ((hR r).mp hr).1))
      exact ⟨a,b,fun _ ↦ ⟨hab,hN⟩⟩
    · exact ⟨r,r,fun hh ↦ (hr hh).elim⟩
  choose a b hN using hchoose
  have hna (r : V) (hr : r ∈ R) : C.toSubgraph.Adj r (a r) := by
    change a r ∈ C.toSubgraph.neighborSet r
    rw [(hN r hr).2]
    exact Or.inl rfl
  have hnb (r : V) (hr : r ∈ R) : C.toSubgraph.Adj r (b r) := by
    change b r ∈ C.toSubgraph.neighborSet r
    rw [(hN r hr).2]
    exact Or.inr rfl
  have hAS : (R : Set V) ⊆ S := fun r hr ↦ ((hR r).mp hr).2
  have ha (r : V) (hr : r ∈ R) : a r ∉ S := fun hh ↦ hInd r (hAS hr) (a r) hh (hna r hr)
  have hb (r : V) (hr : r ∈ R) : b r ∉ S := fun hh ↦ hInd r (hAS hr) (b r) hh (hnb r hr)
  have hF (x : V) (hx : x ∈ S) (y : V) : F.Adj x y ↔ C.toSubgraph.Adj x y := by
    rw [complement_adj_at T i A hx]
    change (T.walk L.index).toSubgraph.Adj x y ↔ L.cycle.toSubgraph.Adj x y
    rw [L.subgraph,Walk.toSubgraph_append,Subgraph.sup_adj]
    constructor
    · rintro (hh|hh)
      · exact hh
      · exact (Set.disjoint_left.mp hTail (L.tail.toSubgraph.edge_vert hh) hx).elim
    · exact Or.inl
  have hfresh (r : V) (hr : r ∈ R) : ¬H.Adj (a r) (b r) := by
    intro hh
    obtain ⟨j,hj,hxy⟩ := hh.1
    have hji : j ≠ i := by
      intro he
      subst j
      change (T.walk L.index).toSubgraph.Adj (a r) (b r) at hxy
      rw [L.subgraph,Walk.toSubgraph_append,Subgraph.sup_adj] at hxy
      rcases hxy with hxyC | hxyT
      · have hl := cycle_length_le_three_of_triangle C hC (hna r hr) hxyC (hnb r hr).symm
        omega
      · have haC : a r ∈ L.cycle.support := Walk.mem_support_of_adj_toSubgraph (hna r hr).symm
        have hbC : b r ∈ L.cycle.support := Walk.mem_support_of_adj_toSubgraph (hnb r hr).symm
        have haT : a r ∈ L.tail.support := Walk.mem_support_of_adj_toSubgraph hxyT
        have hbT : b r ∈ L.tail.support := Walk.mem_support_of_adj_toSubgraph hxyT.symm
        exact (hN r hr).1 ((L.inter _ haC haT).trans (L.inter _ hbC hbT).symm)
    have hrP : r ∉ (T.walk j).support := by
      intro hp
      exact Set.disjoint_left.mp (outside_member_avoids T i A hji (Finset.mem_sdiff.mp hj).2)
        ((T.walk j).mem_verts_toSubgraph.mpr hp) (hAS hr)
    have hrRoot : r ≠ root := by
      rintro rfl
      exact Set.disjoint_left.mp hTail L.tail.start_mem_verts_toSubgraph (hAS hr)
    exact rooted_cycle_avoider_no_chord T hs root L hmin j hji.symm hrRoot
      (hna r hr) (hnb r hr) (hN r hr).1 hrP ((T.walk j).mem_edges_toSubgraph.mp hxy)
  have hinj (r : V) (hr : r ∈ R) (s : V) (hsR : s ∈ R)
      (he : s(a r,b r)=s(a s,b s)) : r=s := by
    by_contra hrs
    have hsa : C.toSubgraph.Adj s (a r) := by
      rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩|⟨h1,h2⟩
      · rw [h1]; exact hna s hsR
      · rw [h1]; exact hnb s hsR
    have hsb : C.toSubgraph.Adj s (b r) := by
      rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩|⟨h1,h2⟩
      · rw [h2]; exact hnb s hsR
      · rw [h2]; exact hna s hsR
    have hl := cycle_length_le_four_of_common_neighbors C hC hrs (hN r hr).1
      (hna r hr) (hnb r hr) hsa hsb
    omega
  have hform : F=H ⊔ spokes R a b := by
    ext x y
    constructor
    · intro hxy
      by_cases hx : x ∈ S
      · have hxC := (hF x hx y).mp hxy
        have hxR : x ∈ R := (hR x).mpr ⟨C.toSubgraph.edge_vert hxC,hx⟩
        have hy : y ∈ ({a x,b x} : Set V) := (hN x hxR).2 ▸ hxC
        apply Or.inr
        apply (spokes_adj R a b x y).mpr
        refine ⟨x,hxR,?_⟩
        rcases hy with hy|hy
        · exact Or.inl ((edge_adj _ _ _ _).mpr ⟨Or.inr ⟨rfl,hy⟩,hxy.ne⟩)
        · exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,hy⟩,hxy.ne⟩)
      · by_cases hy : y ∈ S
        · have hyC := (hF y hy x).mp hxy.symm
          have hyR : y ∈ R := (hR y).mpr ⟨C.toSubgraph.edge_vert hyC,hy⟩
          have hx' : x ∈ ({a y,b y} : Set V) := (hN y hyR).2 ▸ hyC
          apply Or.inr
          apply (spokes_adj R a b x y).mpr
          refine ⟨y,hyR,?_⟩
          rcases hx' with hx'|hx'
          · exact Or.inl ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨hx',rfl⟩,hxy.ne⟩)
          · exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inr ⟨hx',rfl⟩,hxy.ne⟩)
        · exact Or.inl ⟨hxy,hx,hy⟩
    · rintro (hxy|hxy)
      · exact hxy.1
      · obtain ⟨r,hr,hxy|hxy⟩ := (spokes_adj R a b x y).mp hxy
        · have hh := ((hF r (hAS hr) (a r)).mpr (hna r hr)).symm
          rcases (edge_adj _ _ _ _).mp hxy with ⟨⟨h1,h2⟩|⟨h1,h2⟩,_⟩
          · rw [h1,h2]; exact hh
          · rw [h1,h2]; exact hh.symm
        · have hh := (hF r (hAS hr) (b r)).mpr (hnb r hr)
          rcases (edge_adj _ _ _ _).mp hxy with ⟨⟨h1,h2⟩|⟨h1,h2⟩,_⟩
          · rw [h1,h2]; exact hh
          · rw [h1,h2]; exact hh.symm
  exact ⟨R,a,b,hAS,ha,hb,fun r hr ↦ (hN r hr).1,hfresh,hinj,hform⟩


lemma no_independent_zero_component_away_from_tail {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (root : Fin n) (L : RootedCycleRep T root)
    (hmin : ∀ W : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊,
      ∀ M : RootedCycleRep W root, W.score=T.score →
      (∀ z, W.quota z=T.quota z) → L.cycle.length ≤ M.cycle.length)
    (hlen : 4 < L.cycle.length) (A : (normalGraph T L.index).ConnectedComponent)
    (hsize : (selectedGraph T (componentMembers T L.index A)).support.ncard=
      2*(componentMembers T L.index A).card)
    (hTail : Disjoint L.tail.toSubgraph.verts (selectedGraph T (componentMembers T L.index A)).support)
    (hInd : ∀ x ∈ (selectedGraph T (componentMembers T L.index A)).support,
      ∀ y ∈ (selectedGraph T (componentMembers T L.index A)).support, ¬L.cycle.toSubgraph.Adj x y) : False := by
  let B := componentMembers T L.index A
  let S := (selectedGraph T B).support
  let F := selectedGraph T (Finset.univ \ B)
  let H := within F Sᶜ
  have hm := CyclePrefixRepair.maximum_of_one_defect_failure hfail T hs
  have hn := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  obtain ⟨R,a,b,hAS,ha,hb,hab,hfresh,hinj,hform⟩ :=
    independent_tail_avoiding_shortcuts T hs root L hmin hlen A hTail hInd
  have hSn : S.Nonempty := by
    obtain ⟨x,_,hx⟩ := component_meets_removed T hG L.index hn A
    exact ⟨x,hx⟩
  have hSum : S.ncard+Sᶜ.ncard=n := by simpa only [Nat.card_fin] using S.ncard_add_ncard_compl
  have hSp : 0 < S.ncard := hSn.ncard_pos
  have hFc := complement_connected T hG L.index hn A
  have hHS : H.support ⊆ Sᶜ := within_support F Sᶜ
  have hex : ∃ D : Finset F.Subgraph, GoodDecomposition F D ∧ D.card ≤ ⌈(Sᶜ.ncard : ℚ)/2⌉₊ := by
    obtain ⟨D,hD,hDc⟩ := compressed_partition hsmall R a b H S hAS hHS ha hb hab hfresh hinj
      (hform ▸ hFc) (by omega)
    exact Eq.mp (congrArg (fun J : SimpleGraph (Fin n) ↦ ∃ E : Finset J.Subgraph,
      GoodDecomposition J E ∧ E.card ≤ ⌈(Sᶜ.ncard : ℚ)/2⌉₊) hform.symm) ⟨D,hD,hDc⟩
  obtain ⟨D,hD,hDc⟩ := hex
  have hp (j) (hj : j ∉ Finset.univ \ B) : (T.walk j).IsPath := by
    have hjB : j ∈ B := by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hj
    exact (T.one_defect_other_paths hs L.index L.member_not_path).2 j
      ((mem_componentMembers T L.index j A).mp hjB).1
  obtain ⟨E,hE,hEc⟩ := replace_selected T (Finset.univ \ B) hp D hD
  have hcard : (Finset.univ \ B).card=⌈(Fintype.card (Fin n) : ℚ)/2⌉₊-B.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ B)]
    simp only [Finset.card_univ,Fintype.card_fin]
  have hBc : B.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ B
  apply hfail
  refine ⟨E,hE,?_⟩
  rw [hcard] at hEc
  change S.ncard=2*B.card at hsize
  simp only [ceil_half,Fintype.card_fin] at hDc hEc hBc ⊢
  omega

open Erdos583UnifiedMinimalDefectDevelopment in
lemma zero_component_tail_hit_or_cycle_edge (F : MinimalFailure) (D : OptimizedDefect F.graph)
    (hlen : 4 < D.rep.cycle.length)
    (A : (normalGraph D.family D.rep.index).ConnectedComponent)
    (hzero : CycleComponentBudget.componentSurplus D.family D.rep.index A=0) :
    ¬Disjoint D.rep.tail.toSubgraph.verts
      (selectedGraph D.family (componentMembers D.family D.rep.index A)).support ∨
    ∃ x ∈ (selectedGraph D.family (componentMembers D.family D.rep.index A)).support,
      ∃ y ∈ (selectedGraph D.family (componentMembers D.family D.rep.index A)).support,
        D.rep.cycle.toSubgraph.Adj x y := by
  by_contra hnot
  have hTail : Disjoint D.rep.tail.toSubgraph.verts
      (selectedGraph D.family (componentMembers D.family D.rep.index A)).support := by tauto
  have hInd : ∀ x ∈ (selectedGraph D.family (componentMembers D.family D.rep.index A)).support,
      ∀ y ∈ (selectedGraph D.family (componentMembers D.family D.rep.index A)).support,
        ¬D.rep.cycle.toSubgraph.Adj x y := by
    intro x hx y hy hxy
    exact hnot (Or.inr ⟨x,hx,y,hy,hxy⟩)
  have hsize : (selectedGraph D.family (componentMembers D.family D.rep.index A)).support.ncard=
      2*(componentMembers D.family D.rep.index A).card :=
    le_antisymm (Nat.sub_eq_zero_iff_le.mp hzero) (normal_component_expansion F D A)
  exact no_independent_zero_component_away_from_tail F.smaller F.connected F.failure
    D.family D.score D.root D.rep (fun W M hWs _ ↦ D.cycle_minimum W D.root M hWs)
    hlen A hsize hTail hInd

end Erdos583LollipopComponentSuppressionDevelopment
