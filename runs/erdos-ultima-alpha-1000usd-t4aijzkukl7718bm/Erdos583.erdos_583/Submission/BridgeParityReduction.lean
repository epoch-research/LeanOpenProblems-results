import Submission.Work

/-! A bridge in a smallest-order failure must have two odd-degree endpoints.
The forced odd endpoint on one deleted side permits zero-cost leaf extension;
only the other side uses its smaller one-leaf-augmented budget. -/
open SimpleGraph Erdos583Work
open Erdos583Work.BridgeGlue Erdos583Work.VertexCritical
open Erdos583Work.DegreeThreeReduction
namespace Erdos583BridgeParityReductionDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma glue_spanning_cut_sides {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {u v : V} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v)
    (D : Finset (within G (insert v S)).Subgraph)
    (E : Finset (within G (insert u Sᶜ)).Subgraph)
    (hD : GoodDecomposition (within G (insert v S)) D)
    (hE : GoodDecomposition (within G (insert u Sᶜ)) E) :
    ∃ F : Finset G.Subgraph, GoodDecomposition G F ∧ F.card+1 ≤ D.card+E.card := by
  let A := within G (insert v S)
  let B := within G (insert u Sᶜ)
  have hA : A.Adj u v := ⟨h,Set.mem_insert_of_mem _ hu,Set.mem_insert _ _⟩
  have hB : B.Adj u v := ⟨h,Set.mem_insert _ _,Set.mem_insert_of_mem _ hv⟩
  have hcover : A.edgeSet ∪ B.edgeSet=G.edgeSet := by
    ext e
    constructor
    · rintro (he|he)
      · exact edgeSet_mono (within_le _ _) he
      · exact edgeSet_mono (within_le _ _) he
    · induction e using Sym2.ind with
      | h x y =>
        intro he
        by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
        · exact Or.inl ⟨he,Or.inr hx,Or.inr hy⟩
        · obtain ⟨rfl,rfl⟩ := hcross x hx y hy he
          exact Or.inl hA
        · obtain ⟨rfl,rfl⟩ := hcross y hy x hx he.symm
          exact Or.inl hA.symm
        · exact Or.inr ⟨he,Or.inr hx,Or.inr hy⟩
  have hinter : ∀ x ∈ A.support, x ∈ B.support → x=u ∨ x=v := by
    intro x hx hy
    have hx' := within_support G (insert v S) hx
    have hy' := within_support G (insert u Sᶜ) hy
    simp only [Set.mem_insert_iff,Set.mem_compl_iff] at hx' hy'
    tauto
  have hLeafA : ∀ x, A.Adj v x → x=u := by
    intro x hx
    rcases hx.2.2 with hxv | hxS
    · exact (hx.1.ne hxv.symm).elim
    · exact (hcross x hxS v hv hx.1.symm).1
  have hLeafB : ∀ x, B.Adj u x → x=v := by
    intro x hx
    rcases hx.2.2 with hxu | hxS
    · exact (hx.1.ne hxu.symm).elim
    · exact (hcross u hu x hxS hx.1).2
  exact glue_spanning_sides hA hB (within_le _ _) (within_le _ _)
    hcover hinter hLeafA hLeafB D E hD hE

lemma within_bridge_neighbor_add_one {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {u v : V} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v) :
    Nat.card ((within G S).neighborSet u)+1=Nat.card (G.neighborSet u) := by
  have heq : (within G S).neighborSet u=G.neighborSet u \ {v} := by
    ext x
    constructor
    · rintro ⟨hux,_,hx⟩
      exact ⟨hux,fun he ↦ hv (he ▸ hx)⟩
    · rintro ⟨hux,hxv⟩
      refine ⟨hux,hu,?_⟩
      by_contra hx
      exact hxv (hcross u hu x hx hux).2
  simp only [Nat.card_coe_set_eq]
  rw [heq]
  exact Set.ncard_diff_singleton_add_one h

lemma augment_bridge_side_cover {V : Type*} {G : SimpleGraph V}
    (S : Set V) {u v : V} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v) :
    (within G (insert v S)).edgeSet=insert s(v,u) (within G S).edgeSet := by
  ext e
  constructor
  · induction e using Sym2.ind with
    | h x y =>
      change (G.Adj x y ∧ (x=v ∨ x ∈ S) ∧ (y=v ∨ y ∈ S)) → _
      rintro ⟨hxy,hx,hy⟩
      rcases hx with hxv|hx <;> rcases hy with hyv|hy
      · subst x; subst y; exact (G.loopless v hxy).elim
      · subst x
        obtain ⟨rfl,_⟩ := hcross y hy v hv hxy.symm
        exact Or.inl rfl
      · subst y
        obtain ⟨rfl,_⟩ := hcross x hx v hv hxy
        exact Or.inl Sym2.eq_swap
      · exact Or.inr ⟨hxy,hx,hy⟩
  · rintro (rfl|he)
    · exact ⟨h.symm,Or.inl rfl,Or.inr hu⟩
    · induction e using Sym2.ind with
      | h x y => exact ⟨he.1,Or.inr he.2.1,Or.inr he.2.2⟩

lemma extend_even_bridge_side {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {u v : V} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v)
    (heven : Even (Nat.card (G.neighborSet u)))
    (D : Finset (G.induce S).Subgraph) (hD : GoodDecomposition (G.induce S) D) :
    ∃ E : Finset (within G (insert v S)).Subgraph,
      GoodDecomposition (within G (insert v S)) E ∧ E.card ≤ D.card := by
  have hodd : Odd (Nat.card ((within G S).neighborSet u)) := by
    have he := within_bridge_neighbor_add_one S h hu hv hcross
    rw [←he] at heven
    exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp heven)
  obtain ⟨D',hD',hDc⟩ := lift_induce_within S D hD
  obtain ⟨E,hE,hEc⟩ := append_at_odd_to_isolated
    (show within G S ≤ within G (insert v S) from fun _ _ hx ↦
      ⟨hx.1,Or.inr hx.2.1,Or.inr hx.2.2⟩)
    (show (within G (insert v S)).Adj v u from ⟨h.symm,Or.inl rfl,Or.inr hu⟩)
    (fun _ hx ↦ hv hx.2.1) hodd (augment_bridge_side_cover S h hu hv hcross) D' hD'
  exact ⟨E,hE,hEc.trans hDc⟩

lemma gallai_of_even_bridge_endpoint {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected) {u v : Fin n}
    (hbr : G.IsBridge s(u,v)) (heven : Even (Nat.card (G.neighborSet u))) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  have h := (isBridge_iff.mp hbr).1
  obtain ⟨S,hu,hv,hcross⟩ := bridge_cut hbr
  have hSpos : 0 < S.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨u,hu⟩
  have hTpos : 0 < Sᶜ.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨v,hv⟩
  have hS : 2 ≤ S.ncard := by
    by_contra hn
    have he := cut_singleton_degree S h hu hcross (by omega)
    rw [he] at heven
    exact (by decide : ¬Even (1 : ℕ)) heven
  have hsum : S.ncard+Sᶜ.ncard=n := by simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using S.ncard_add_ncard_compl
  have hcross' : ∀ x ∈ Sᶜ, ∀ y ∉ Sᶜ, G.Adj x y → x=v ∧ y=u := by
    intro x hx y hy hxy
    have hyS : y ∈ S := by simpa only [Set.mem_compl_iff,not_not] using hy
    exact (hcross y hyS x hx hxy.symm).symm
  have hconnS := CutVertexReduction.single_boundary_connected hG S u hu
    (fun x hx y hy hxy ↦ (hcross x hx y hy hxy).1)
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce G S (by omega) hconnS
  obtain ⟨D',hD',hD'c⟩ := extend_even_bridge_side S h hu hv hcross heven D hD
  have hconnT := cut_side_connected hG Sᶜ h.symm hv (not_not.mpr hu) hcross'
  have hsizeT : (insert u Sᶜ).ncard=Sᶜ.ncard+1 := Set.ncard_insert_of_notMem (not_not.mpr hu)
  obtain ⟨E,hE,hEc⟩ := hsmall.on_induce G (insert u Sᶜ) (by rw [hsizeT]; omega) hconnT
  obtain ⟨E',hE',hE'c⟩ := lift_induce_within (insert u Sᶜ) E hE
  obtain ⟨F,hF,hFc⟩ := glue_spanning_cut_sides S h hu hv hcross D' E' hD' hE'
  rw [ceil_half] at hDc
  rw [hsizeT,ceil_half] at hEc
  exact ⟨F,hF,by simp only [Fintype.card_fin,ceil_half]; omega⟩

lemma bridge_endpoints_odd_of_failure {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (hbr : G.IsBridge s(u,v)) :
    Odd (Nat.card (G.neighborSet u)) ∧ Odd (Nat.card (G.neighborSet v)) := by
  constructor
  · apply Nat.not_even_iff_odd.mp
    intro he
    exact hfail (gallai_of_even_bridge_endpoint hsmall hG hbr he)
  · apply Nat.not_even_iff_odd.mp
    intro he
    apply hfail
    exact gallai_of_even_bridge_endpoint hsmall hG
      (show G.IsBridge s(v,u) from by simpa only [Sym2.eq_swap] using hbr) he

lemma even_vertex_no_bridge_of_failure {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u : Fin n} (hu : Even (Nat.card (G.neighborSet u))) (v : Fin n) :
    ¬G.IsBridge s(u,v) := by
  intro hbr
  exact Nat.not_even_iff_odd.mpr (bridge_endpoints_odd_of_failure hsmall hG hfail hbr).1 hu

/-- At a witness minimal by order and then by edges, the additional even-forest
hypothesis forces the even vertices to be independent.  No inheritance of the
hypothesis under arbitrary edge deletion is asserted. -/
lemma even_forest_independent_of_failure {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hcritical : EdgeCritical.EdgeMinimal G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hf : (G.induce {v | Even (Nat.card (G.neighborSet v))}).IsAcyclic)
    {u v : Fin n} (hu : Even (Nat.card (G.neighborSet u)))
    (hv : Even (Nat.card (G.neighborSet v))) : ¬G.Adj u v := by
  intro h
  have hb := hcritical.even_even_edge_isBridge_of_even_forest hG hfail hf h hv hu
  exact even_vertex_no_bridge_of_failure hsmall hG hfail hu v hb

end Erdos583BridgeParityReductionDevelopment
