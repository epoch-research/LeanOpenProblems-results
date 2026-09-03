import Submission.Work

/-! Smaller-order path budgets can be summed over disconnected even-order
components. Isolated vertices are removed before the support-budget version. -/
namespace Erdos583ComponentBudgetDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 1600000

lemma partition_components {V : Type*} [Fintype V] (G : SimpleGraph V)
    (b : G.ConnectedComponent → ℕ)
    (hparts : ∀ C : G.ConnectedComponent, ∃ D : Finset (G.induce C.supp).Subgraph,
      GoodDecomposition (G.induce C.supp) D ∧ D.card ≤ b C) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ∑ C, b C := by
  classical
  have hex (C : G.ConnectedComponent) : ∃ D : Finset G.Subgraph,
      (∀ K ∈ D, IsPathSubgraph K) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun K ↦ K.edgeSet) ∧
      (⋃ K ∈ D, K.edgeSet)=(within G C.supp).edgeSet ∧ D.card ≤ b C := by
    obtain ⟨D,hD,hDc⟩ := hparts C
    obtain ⟨E,hE,hEc⟩ := lift_induce_within C.supp D hD
    let hle := within_le G C.supp
    refine ⟨E.image (Subgraph.map (Hom.ofLE hle)),?_,hE.2.lift_pairwise hle,
      hE.2.lift_union hle,Finset.card_image_le.trans (hEc.trans hDc)⟩
    intro K hK
    obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hK
    exact lift_path_subgraph hle (hE.1 L hL)
  choose D hp hd hcov hcard using hex
  let E := Finset.univ.biUnion D
  have hsub (C : G.ConnectedComponent) (K : G.Subgraph) (hK : K ∈ D C) :
      K.edgeSet ⊆ (within G C.supp).edgeSet := by
    intro e he
    rw [←hcov C]
    exact Set.mem_iUnion.mpr ⟨K,Set.mem_iUnion.mpr ⟨hK,he⟩⟩
  have hsep {C C' : G.ConnectedComponent} (hne : C ≠ C') :
      Disjoint (within G C.supp).edgeSet (within G C'.supp).edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he he'
    induction e using Sym2.ind with
    | h x y => exact hne (ConnectedComponent.eq_of_common_vertex he.2.1 he'.2.1)
  refine ⟨E,⟨?_,?_,?_⟩,?_⟩
  · intro K hK
    obtain ⟨C,_,hK⟩ := Finset.mem_biUnion.mp hK
    exact hp C K hK
  · intro K hK L hL hKL
    obtain ⟨C,_,hK⟩ := Finset.mem_biUnion.mp hK
    obtain ⟨C',_,hL⟩ := Finset.mem_biUnion.mp hL
    by_cases hCC : C=C'
    · subst C'; exact hd C hK hL hKL
    · exact (hsep hCC).mono (hsub C K hK) (hsub C' L hL)
  · ext e
    constructor
    · intro hh
      obtain ⟨K,hK⟩ := Set.mem_iUnion.mp hh
      obtain ⟨_,he⟩ := Set.mem_iUnion.mp hK
      exact K.edgeSet_subset he
    · intro he
      induction e using Sym2.ind with
      | h x y =>
        let C := G.connectedComponentMk x
        have hx : x ∈ C.supp := rfl
        have hy : y ∈ C.supp := (C.mem_supp_congr_adj he).mp hx
        have hc : s(x,y) ∈ ⋃ K ∈ D C, K.edgeSet := (hcov C).symm ▸ ⟨he,hx,hy⟩
        simp only [Set.mem_iUnion] at hc
        obtain ⟨K,hK,hKe⟩ := hc
        exact Set.mem_iUnion.mpr ⟨K,Set.mem_iUnion.mpr
          ⟨Finset.mem_biUnion.mpr ⟨C,Finset.mem_univ C,hK⟩,hKe⟩⟩
  · exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun C _ ↦ hcard C)

lemma sum_component_orders {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∑ C : G.ConnectedComponent, C.supp.ncard=Fintype.card V := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
    (f := G.connectedComponentMk) (fun _ _ ↦ Finset.mem_univ _)
  have hf (C : G.ConnectedComponent) :
      (Finset.univ.filter fun v ↦ G.connectedComponentMk v=C).card=C.supp.ncard := by
    have he : (Finset.univ.filter fun v ↦ G.connectedComponentMk v=C)=C.supp.toFinset := by
      ext v; simp
    rw [he,Set.toFinset_card,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  simpa only [Finset.card_univ,hf] using h.symm

lemma smaller_orders_even_components {n : ℕ} (hsmall : SmallerOrders n)
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hsize : Fintype.card V < n)
    (heven : ∀ C : G.ConnectedComponent, Even C.supp.ncard) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card ≤ Fintype.card V := by
  classical
  obtain ⟨D,hD,hDc⟩ := partition_components G (fun C ↦ ⌈(C.supp.ncard : ℚ)/2⌉₊) (by
    intro C
    exact hsmall.on_induce G C.supp ((C.supp.ncard_le_card.trans_eq (Nat.card_eq_fintype_card)).trans_lt hsize)
      C.connected_toSimpleGraph)
  have hbudget (C : G.ConnectedComponent) : 2*⌈(C.supp.ncard : ℚ)/2⌉₊=C.supp.ncard := by
    obtain ⟨m,hm⟩ := heven C
    rw [ceil_half]
    omega
  refine ⟨D,hD,(Nat.mul_le_mul_left 2 hDc).trans ?_⟩
  rw [Finset.mul_sum]
  simp_rw [hbudget]
  exact (sum_component_orders G).le

lemma smaller_orders_even_support {n : ℕ} (hsmall : SmallerOrders n)
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hsize : G.support.ncard < n)
    (heven : ∀ C : (G.induce G.support).ConnectedComponent, Even C.supp.ncard) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card ≤ G.support.ncard := by
  classical
  have hc : Fintype.card G.support=G.support.ncard := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  obtain ⟨D,hD,hDc⟩ := smaller_orders_even_components hsmall (G.induce G.support) (by simpa [hc] using hsize) heven
  obtain ⟨E,hE,hEc⟩ := hD.lift_induce_support G
  exact ⟨E,hE,(Nat.mul_le_mul_left 2 hEc).trans (by simpa [hc] using hDc)⟩

lemma restore_path_even_components {n : ℕ} (hsmall : SmallerOrders n)
    (G : SimpleGraph (Fin n)) {a b : Fin n} (P : G.Walk a b) (hp : P.IsPath)
    (hsize : (G.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ n)
    (heven : let H := G.deleteEdges P.toSubgraph.edgeSet
      ∀ C : (H.induce H.support).ConnectedComponent, Even C.supp.ncard) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  obtain ⟨D,hD,hDc⟩ := smaller_orders_even_support hsmall (G.deleteEdges P.toSubgraph.edgeSet) (by omega) heven
  obtain ⟨E,hE,hEc⟩ := restore_path_subgraph ⟨_,_,P,hp,rfl⟩ hD
  refine ⟨E,hE,?_⟩
  simp only [Fintype.card_fin,ceil_half]
  omega

/-- A restoring path that isolates at least two vertices in a smallest
failure must leave an odd-order NONTRIVIAL component. Isolated vertices are
not counted as obstructions. -/
lemma failure_path_leaves_odd_component {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {a b : Fin n} (P : G.Walk a b) (hp : P.IsPath)
    (hsize : (G.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ n) :
    let H := G.deleteEdges P.toSubgraph.edgeSet
    ∃ C : (H.induce H.support).ConnectedComponent, Odd C.supp.ncard := by
  dsimp only
  by_contra! hn
  apply hfail
  apply restore_path_even_components hsmall G P hp hsize
  dsimp only
  intro C
  exact Nat.not_odd_iff_even.mp (hn C)

lemma support_component_order_ge_two {V : Type*} [Fintype V] (G : SimpleGraph V)
    (C : (G.induce G.support).ConnectedComponent) : 2 ≤ C.supp.ncard := by
  obtain ⟨x,hx⟩ := C.nonempty_supp
  obtain ⟨y,hxy⟩ := G.mem_support.mp x.property
  let y' : G.support := ⟨y,G.mem_support.mpr ⟨x.val,hxy.symm⟩⟩
  have hy : y' ∈ C.supp := (C.mem_supp_congr_adj (show (G.induce G.support).Adj x y' from hxy)).mp hx
  have hne : x ≠ y' := fun h ↦ hxy.ne (congrArg Subtype.val h)
  have hcard := (Set.one_lt_ncard_iff (Set.toFinite C.supp)).mpr ⟨x,y',hx,hy,hne⟩
  omega

lemma failure_path_leaves_large_odd_component {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {a b : Fin n} (P : G.Walk a b) (hp : P.IsPath)
    (hsize : (G.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ n) :
    let H := G.deleteEdges P.toSubgraph.edgeSet
    ∃ C : (H.induce H.support).ConnectedComponent, Odd C.supp.ncard ∧ 3 ≤ C.supp.ncard := by
  obtain ⟨C,hC⟩ := failure_path_leaves_odd_component hsmall hfail P hp hsize
  have hc := support_component_order_ge_two (G.deleteEdges P.toSubgraph.edgeSet) C
  refine ⟨C,hC,?_⟩
  obtain ⟨m,hm⟩ := hC
  omega

end Erdos583ComponentBudgetDevelopment
