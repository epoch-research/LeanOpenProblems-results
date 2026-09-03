import Submission.Work

/-! Sharp one-even-vertex components offset the rounding losses in component
budgets. Remaining losses are confined to odd components with at least three
even-degree vertices. All degrees here are internal to the component. -/
namespace Erdos583ComponentDeficitDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 1600000

noncomputable def evenCount {V : Type*} (G : SimpleGraph V) : ℕ :=
  {v | Even (Nat.card (G.neighborSet v))}.ncard

lemma evenCount_eq_filter {V : Type*} [Fintype V] (G : SimpleGraph V) :
    evenCount G=(Finset.univ.filter fun v ↦ Even (Nat.card (G.neighborSet v))).card := by
  classical
  rw [evenCount,Set.ncard_eq_toFinset_card']
  congr 1
  ext v
  simp

lemma odd_order_iff_evenCount_odd {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Odd (Fintype.card V) ↔ Odd (evenCount G) := by
  classical
  have hs := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun v ↦ Even (Nat.card (G.neighborSet v)))
  simp only [Nat.not_even_iff_odd,Finset.card_univ,←evenCount_eq_filter] at hs
  have he : Even (Finset.univ.filter fun v ↦ Odd (Nat.card (G.neighborSet v))).card := by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using G.even_card_odd_degree_vertices
  obtain ⟨m,hm⟩ := he
  rw [Nat.odd_iff,Nat.odd_iff]
  omega

lemma component_neighbor_card {V : Type*} {G : SimpleGraph V}
    (C : G.ConnectedComponent) (x : C.supp) :
    Nat.card ((G.induce C.supp).neighborSet x)=Nat.card (G.neighborSet x.val) := by
  rw [CutVertexParity.induced_neighbor_card]
  have hs : G.neighborSet x.val ⊆ C.supp :=
    fun y hy ↦ (C.mem_supp_congr_adj hy).mp x.property
  rw [Set.inter_eq_left.mpr hs,←Nat.card_coe_set_eq]

lemma component_evenCount_eq {V : Type*} {G : SimpleGraph V}
    (C : G.ConnectedComponent) :
    evenCount (G.induce C.supp)=
      {v | Even (Nat.card (G.neighborSet v)) ∧ G.connectedComponentMk v=C}.ncard := by
  let e : {x : C.supp // Even (Nat.card ((G.induce C.supp).neighborSet x))} ≃
      {v | Even (Nat.card (G.neighborSet v)) ∧ G.connectedComponentMk v=C} :=
    { toFun := fun x ↦ ⟨x.val.val,by simpa only [component_neighbor_card] using x.property,x.val.property⟩
      invFun := fun x ↦ ⟨⟨x.val,x.property.2⟩,by rw [component_neighbor_card]; exact x.property.1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  unfold evenCount
  rw [←Nat.card_coe_set_eq,←Nat.card_coe_set_eq]
  exact Nat.card_congr e

lemma sum_component_evenCounts {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∑ C : G.ConnectedComponent, evenCount (G.induce C.supp)=evenCount G := by
  classical
  let S := Finset.univ.filter fun v ↦ Even (Nat.card (G.neighborSet v))
  have h := Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.univ)
    (f := G.connectedComponentMk) (fun _ _ ↦ Finset.mem_univ _)
  have hf (C : G.ConnectedComponent) :
      (S.filter fun v ↦ G.connectedComponentMk v=C).card=evenCount (G.induce C.supp) := by
    rw [component_evenCount_eq,Set.ncard_eq_toFinset_card']
    congr 1
    ext v
    simp [S]
  have hS : S.card=evenCount G := (evenCount_eq_filter G).symm
  simpa only [hf,hS] using h.symm

lemma sharp_one_even_partition {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : evenCount G=1) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card+1=Fintype.card V := by
  obtain ⟨v,hv⟩ := Set.ncard_eq_one.mp h
  have he : Even (Nat.card (G.neighborSet v)) := by
    have hm : v ∈ ({v} : Set V) := rfl
    rwa [←hv] at hm
  have ho : ∀ x, x ≠ v → Odd (Nat.card (G.neighborSet x)) := by
    intro x hx
    apply Nat.not_even_iff_odd.mp
    intro hh
    have hm : x ∈ ({v} : Set V) := hv ▸ hh
    exact hx hm
  obtain ⟨D,hD,_,_,hc⟩ := MarkedBudgets.one_even_path_partition G v he ho
  exact ⟨D,hD,hc⟩

/-- Components whose odd order may cost a rounding-up unit, after removing
components with the sharp one-even-vertex formula. -/
def BadComponent {V : Type*} (G : SimpleGraph V) (C : G.ConnectedComponent) : Prop :=
  Odd C.supp.ncard ∧ evenCount (G.induce C.supp) ≠ 1

noncomputable def badCount {V : Type*} (G : SimpleGraph V) : ℕ :=
  {C | BadComponent G C}.ncard

lemma badCount_eq_filter {V : Type*} [Fintype V] (G : SimpleGraph V) :
    badCount G=(Finset.univ.filter (BadComponent G)).card := by
  classical
  rw [badCount,Set.ncard_eq_toFinset_card']
  congr 1
  ext C
  simp

lemma bad_component_three_even {V : Type*} [Fintype V] {G : SimpleGraph V}
    {C : G.ConnectedComponent} (hC : BadComponent G C) :
    3 ≤ evenCount (G.induce C.supp) := by
  classical
  have hc : Fintype.card C.supp=C.supp.ncard := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have ho : Odd (evenCount (G.induce C.supp)) :=
    (odd_order_iff_evenCount_odd (G.induce C.supp)).mp (by rw [hc]; exact hC.1)
  obtain ⟨m,hm⟩ := ho
  have hn := hC.2
  omega

lemma three_badCount_le_evenCount {V : Type*} [Fintype V] (G : SimpleGraph V) :
    3*badCount G ≤ evenCount G := by
  classical
  have hbound (C : G.ConnectedComponent) :
      3*(if BadComponent G C then 1 else 0) ≤ evenCount (G.induce C.supp) := by
    split_ifs with h
    · simpa using bad_component_three_even h
    · simp
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun C _ ↦ hbound C)
  rw [←Finset.mul_sum,←Finset.card_filter,sum_component_evenCounts] at hs
  simpa only [badCount_eq_filter] using hs

lemma component_deficit_budget {n : ℕ} (hsmall : SmallerOrders n)
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hsize : ∀ C : G.ConnectedComponent, C.supp.ncard < n) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      2*D.card ≤ Fintype.card V+badCount G := by
  classical
  let b := fun C : G.ConnectedComponent ↦
    if evenCount (G.induce C.supp)=1 then (C.supp.ncard-1)/2 else ⌈(C.supp.ncard : ℚ)/2⌉₊
  have hparts (C : G.ConnectedComponent) : ∃ D : Finset (G.induce C.supp).Subgraph,
      GoodDecomposition (G.induce C.supp) D ∧ D.card ≤ b C := by
    by_cases hC : evenCount (G.induce C.supp)=1
    · obtain ⟨D,hD,hDc⟩ := sharp_one_even_partition (G.induce C.supp) hC
      have hc : Fintype.card C.supp=C.supp.ncard := by
        rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
      rw [hc] at hDc
      refine ⟨D,hD,?_⟩
      simp only [b,if_pos hC]
      omega
    · simpa only [b,if_neg hC] using hsmall.on_induce G C.supp (hsize C) C.connected_toSimpleGraph
  obtain ⟨D,hD,hDc⟩ := ComponentBudget.partition_components G b hparts
  have hbound (C : G.ConnectedComponent) :
      2*b C ≤ C.supp.ncard+(if BadComponent G C then 1 else 0) := by
    by_cases hC : evenCount (G.induce C.supp)=1
    · simp only [b,if_pos hC,BadComponent,hC,ne_eq,not_true_eq_false,and_false,if_false,add_zero]
      omega
    · by_cases ho : Odd C.supp.ncard
      · have hb : BadComponent G C := ⟨ho,hC⟩
        simp only [b,if_neg hC,if_pos hb,ceil_half]
        omega
      · have he : C.supp.ncard%2=0 := Nat.even_iff.mp (Nat.not_odd_iff_even.mp ho)
        simp only [b,if_neg hC,BadComponent,ho,false_and,if_false,add_zero,ceil_half]
        omega
  refine ⟨D,hD,(Nat.mul_le_mul_left 2 hDc).trans ?_⟩
  rw [Finset.mul_sum]
  calc
    ∑ C, 2*b C ≤ ∑ C, (C.supp.ncard+(if BadComponent G C then 1 else 0)) :=
      Finset.sum_le_sum (fun C _ ↦ hbound C)
    _ = Fintype.card V+badCount G := by
      rw [Finset.sum_add_distrib,ComponentBudget.sum_component_orders,←Finset.card_filter,
        badCount_eq_filter]

lemma component_budget_of_one_bad {n : ℕ} (hsmall : SmallerOrders n)
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hsize : ∀ C : G.ConnectedComponent, C.supp.ncard < n) (hb : badCount G ≤ 1) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  obtain ⟨D,hD,hDc⟩ := component_deficit_budget hsmall G hsize
  refine ⟨D,hD,?_⟩
  rw [ceil_half]
  omega

/-- Summing proper-component budgets loses at most one half-unit when there
are at most five even-degree vertices, so it still meets the global ceiling.
This does not assert the connected case at the critical order. -/
lemma component_budget_of_five_even {n : ℕ} (hsmall : SmallerOrders n)
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hsize : ∀ C : G.ConnectedComponent, C.supp.ncard < n) (he : evenCount G ≤ 5) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  apply component_budget_of_one_bad hsmall G hsize
  have hb := three_badCount_le_evenCount G
  omega

lemma support_budget_of_one_bad {n : ℕ} (hsmall : SmallerOrders n)
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hsize : G.support.ncard < n)
    (hb : badCount (G.induce G.support) ≤ 1) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(G.support.ncard : ℚ)/2⌉₊ := by
  classical
  have hc : Fintype.card G.support=G.support.ncard := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hs (C : (G.induce G.support).ConnectedComponent) : C.supp.ncard < n := by
    have hle := C.supp.ncard_le_card
    rw [Nat.card_eq_fintype_card,hc] at hle
    omega
  obtain ⟨D,hD,hDc⟩ := component_budget_of_one_bad hsmall (G.induce G.support) hs hb
  obtain ⟨E,hE,hEc⟩ := hD.lift_induce_support G
  exact ⟨E,hE,hEc.trans (by simpa only [hc] using hDc)⟩

lemma restore_path_one_bad_component {n : ℕ} (hsmall : SmallerOrders n)
    (G : SimpleGraph (Fin n)) {a b : Fin n} (P : G.Walk a b) (hp : P.IsPath)
    (hsize : (G.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ n)
    (hb : let H := G.deleteEdges P.toSubgraph.edgeSet
      badCount (H.induce H.support) ≤ 1) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  obtain ⟨D,hD,hDc⟩ := support_budget_of_one_bad hsmall (G.deleteEdges P.toSubgraph.edgeSet) (by omega) hb
  obtain ⟨E,hE,hEc⟩ := restore_path_subgraph ⟨_,_,P,hp,rfl⟩ hD
  refine ⟨E,hE,?_⟩
  rw [ceil_half] at hDc
  simp only [Fintype.card_fin,ceil_half]
  omega

lemma restore_path_five_even_support {n : ℕ} (hsmall : SmallerOrders n)
    (G : SimpleGraph (Fin n)) {a b : Fin n} (P : G.Walk a b) (hp : P.IsPath)
    (hsize : (G.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ n)
    (he : let H := G.deleteEdges P.toSubgraph.edgeSet
      evenCount (H.induce H.support) ≤ 5) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  apply restore_path_one_bad_component hsmall G P hp hsize
  dsimp only
  have hb := three_badCount_le_evenCount
    ((G.deleteEdges P.toSubgraph.edgeSet).induce (G.deleteEdges P.toSubgraph.edgeSet).support)
  dsimp only at he
  omega

lemma failure_path_two_bad_components {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {a b : Fin n} (P : G.Walk a b) (hp : P.IsPath)
    (hsize : (G.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ n) :
    let H := G.deleteEdges P.toSubgraph.edgeSet
    2 ≤ badCount (H.induce H.support) := by
  dsimp only
  by_contra hn
  apply hfail
  apply restore_path_one_bad_component hsmall G P hp hsize
  dsimp only
  omega

/-- The relevant even vertices are measured AFTER path deletion and inside
the non-isolated support, not in the original graph. -/
lemma failure_path_six_even_support {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {a b : Fin n} (P : G.Walk a b) (hp : P.IsPath)
    (hsize : (G.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ n) :
    let H := G.deleteEdges P.toSubgraph.edgeSet
    6 ≤ evenCount (H.induce H.support) := by
  have hb := failure_path_two_bad_components hsmall hfail P hp hsize
  have he := three_badCount_le_evenCount
    ((G.deleteEdges P.toSubgraph.edgeSet).induce (G.deleteEdges P.toSubgraph.edgeSet).support)
  dsimp only at hb ⊢
  omega

lemma failure_path_two_odd_even_rich_components {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {a b : Fin n} (P : G.Walk a b) (hp : P.IsPath)
    (hsize : (G.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ n) :
    let H := G.deleteEdges P.toSubgraph.edgeSet
    let J := H.induce H.support
    ∃ C D : J.ConnectedComponent, C ≠ D ∧ Odd C.supp.ncard ∧ Odd D.supp.ncard ∧
      3 ≤ evenCount (J.induce C.supp) ∧ 3 ≤ evenCount (J.induce D.supp) := by
  classical
  dsimp only
  let J := (G.deleteEdges P.toSubgraph.edgeSet).induce (G.deleteEdges P.toSubgraph.edgeSet).support
  have hb := failure_path_two_bad_components hsmall hfail P hp hsize
  have hcard : 1 < {C | BadComponent J C}.ncard := by
    change 2 ≤ {C | BadComponent J C}.ncard at hb
    omega
  obtain ⟨C,D,hbadC,hbadD,hCD⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp hcard
  exact ⟨C,D,hCD,hbadC.1,hbadD.1,bad_component_three_even hbadC,bad_component_three_even hbadD⟩

end Erdos583ComponentDeficitDevelopment
