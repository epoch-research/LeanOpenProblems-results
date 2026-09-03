import Submission.Work

/-! Restoring a cubic neighbor of a leaf when one of its other neighbors
has even ambient degree. -/
namespace Erdos583LeafCubicEvenDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.VertexCritical Erdos583Work.BridgeGlue Erdos583Work.LeafPairReduction
open Erdos583Work.DegreeThreeReduction
open scoped Classical
set_option maxHeartbeats 1800000

lemma leaf_cubic_even_neighbor_reduction {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    {u v a b : Fin n} (huv : G.Adj u v) (ha : G.Adj v a) (hb : G.Adj v b)
    (hab : G.Adj a b) (hau : a ≠ u) (hbu : b ≠ u)
    (hu : ∀ x, G.Adj u x → x=v)
    (hv : ∀ x, G.Adj v x → x=u ∨ x=a ∨ x=b)
    (heven : Even (Nat.card (G.neighborSet a))) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let S : Set (Fin n) := {u,v}ᶜ
  let A := within G S
  let C := G.deleteEdges {s(v,b)}
  let B := C.deleteEdges {s(u,v)}
  have haS : a ∈ S := by simp [S,hau,ha.ne.symm]
  have hconn : (G.induce S).Connected := DegreeTwoPacking.induce_dominated_boundary_connected hG {u,v} haS (by
    intro x hx y hy hxy
    rcases hx with hx|hx
    · subst x
      exact (hy (Or.inr (hu y hxy))).elim
    · have hx : x=v := hx
      subst x
      rcases hv y hxy with hy'|hy'|hy'
      · exact (hy (Or.inl hy')).elim
      · exact Or.inl hy'
      · subst y; exact Or.inr hab)
  have hAN : A.neighborSet a=G.neighborSet a \ {v} := by
    ext x
    constructor
    · rintro ⟨hax,_,hx⟩
      exact ⟨hax,fun he ↦ hx (Or.inr he)⟩
    · rintro ⟨hax,hxv⟩
      have hxu : x ≠ u := by
        rintro rfl
        exact ha.ne (hu a hax.symm).symm
      exact ⟨hax,haS,by simp [S,hxu,hxv]⟩
  have hAdeg : Nat.card (A.neighborSet a)+1=Nat.card (G.neighborSet a) := by
    simp only [Nat.card_coe_set_eq]
    rw [hAN]
    exact Set.ncard_diff_singleton_add_one ha.symm
  have hAo : Odd (Nat.card (A.neighborSet a)) := by
    rw [←hAdeg] at heven
    exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp heven)
  have hCuv : C.Adj u v := by
    simp only [C,deleteEdges_adj,Set.mem_singleton_iff]
    refine ⟨huv,?_⟩
    simp [huv.ne,hbu.symm]
  have hCu : ∀ x, C.Adj u x → x=v := fun x hx ↦ hu x (deleteEdges_adj.mp hx).1
  have hBiso : ∀ x, ¬B.Adj u x := by
    intro x hx
    have hh := deleteEdges_adj.mp hx
    exact hh.2 (by rw [hCu x hh.1]; rfl)
  have hBva : B.Adj v a := by
    simp only [B,C,deleteEdges_adj,Set.mem_singleton_iff]
    refine ⟨⟨ha,?_⟩,?_⟩
    · simp [hab.ne,hb.ne]
    · simp [huv.ne.symm,hau]
  have hBv : ∀ x, B.Adj v x → x=a := by
    intro x hx
    have h1 := deleteEdges_adj.mp hx
    have h2 := deleteEdges_adj.mp h1.1
    rcases hv x h2.1 with hx|hx|hx
    · exact (h1.2 (by simp [hx,Sym2.eq_swap])).elim
    · exact hx
    · exact (h2.2 (by simp [hx])).elim
  have hBdeg : Nat.card (B.neighborSet v)=1 := by
    have heq : B.neighborSet v={a} := by ext x; exact ⟨hBv x,fun hx ↦ hx ▸ hBva⟩
    rw [heq,Nat.card_coe_set_eq,Set.ncard_singleton]
  have hBA : within B ({v}ᶜ : Set (Fin n))=A := by
    ext x y
    constructor
    · rintro ⟨hxy,hxv,hyv⟩
      change x ≠ v at hxv
      change y ≠ v at hyv
      have hxu : x ≠ u := by rintro rfl; exact hBiso y hxy
      have hyu : y ≠ u := by rintro rfl; exact hBiso x hxy.symm
      exact ⟨(deleteEdges_adj.mp (deleteEdges_adj.mp hxy).1).1,
        by simp [S,hxu,hxv],by simp [S,hyu,hyv]⟩
    · rintro ⟨hxy,hx,hy⟩
      have hxu : x ≠ u := fun he ↦ hx (Or.inl he)
      have hxv : x ≠ v := fun he ↦ hx (Or.inr he)
      have hyu : y ≠ u := fun he ↦ hy (Or.inl he)
      have hyv : y ≠ v := fun he ↦ hy (Or.inr he)
      refine ⟨?_,hxv,hyv⟩
      simp only [B,C,deleteEdges_adj,Set.mem_singleton_iff]
      exact ⟨⟨hxy,by simp [hxv,hyv]⟩,by simp [hxu,hyu]⟩
  have hAB : A ≤ B := by rw [←hBA]; exact within_le _ _
  have hAiso : ∀ x, ¬A.Adj v x := fun x hx ↦ hx.2.1 (Or.inr rfl)
  have hBcover : B.edgeSet=insert s(v,a) A.edgeSet := by
    rw [←hBA,LeafReduction.within_delete_leaf hBv]
    conv_rhs => rw [edgeSet_deleteEdges]
    rw [Set.insert_diff_singleton,Set.insert_eq_of_mem (show s(v,a) ∈ B.edgeSet from hBva)]
  have hCcover : C.edgeSet=insert s(u,v) B.edgeSet := by
    change C.edgeSet=insert s(u,v) (C.deleteEdges {s(u,v)}).edgeSet
    conv_rhs => rw [edgeSet_deleteEdges]
    rw [Set.insert_diff_singleton,Set.insert_eq_of_mem (show s(u,v) ∈ C.edgeSet from hCuv)]
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce G S (two_removed_lt huv.ne) hconn
  obtain ⟨D',hD',hD'c⟩ := lift_induce_within S D hD
  obtain ⟨E,hE,hEc⟩ := append_at_odd_to_isolated hAB hBva hAiso hAo hBcover D' hD'
  obtain ⟨F,hF,hFc⟩ := append_at_odd_to_isolated (show B ≤ C from deleteEdges_le _)
    hCuv hBiso (by rw [hBdeg]; exact ⟨0,rfl⟩) hCcover E hE
  obtain ⟨K,hK,hKc⟩ := restore_edge hb hF
  exact ⟨K,hK,two_removed_budget huv.ne hDc (by omega)⟩

lemma cubic_leaf_neighbors_odd {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (huv : G.Adj u v) (hu : ∀ x, G.Adj u x → x=v)
    (hd : Nat.card (G.neighborSet v)=3) :
    ∀ x, G.Adj v x → Odd (Nat.card (G.neighborSet x)) := by
  obtain ⟨a,b,ha,hb,hab,hau,hbu,habG,hv⟩ :=
    LeafCubicReduction.leaf_cubic_triangle_of_failure hsmall hG hfail huv hu hd
  intro x hx
  rcases hv x hx with hx|hx|hx
  · subst x
    have heq : G.neighborSet u={v} := by ext z; exact ⟨hu z,fun hz ↦ hz ▸ huv⟩
    rw [heq,Nat.card_coe_set_eq,Set.ncard_singleton]
    exact ⟨0,rfl⟩
  · subst x
    apply Nat.not_even_iff_odd.mp
    intro heven
    exact hfail (leaf_cubic_even_neighbor_reduction hsmall hG huv ha hb habG hau hbu hu hv heven)
  · subst x
    apply Nat.not_even_iff_odd.mp
    intro heven
    exact hfail (leaf_cubic_even_neighbor_reduction hsmall hG huv hb ha habG.symm hbu hau hu
      (fun z hz ↦ by rcases hv z hz with h|h|h; exact Or.inl h; exact Or.inr (Or.inr h); exact Or.inr (Or.inl h)) heven)

lemma cubic_root_no_leaf_neighbor {n k : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : QuotaTrails.TrailFamily G k) (r : Fin n)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : QuotaTrails.TrailFamily G k, U.score ≤ T.score)
    (hroot : QuotaRooted.HasRoot T r) (hd : Nat.card (G.neighborSet r)=3)
    {b : Fin n} (hrb : G.Adj r b) (hb : Nat.card (G.neighborSet b)=1) : False := by
  obtain ⟨a,_,ha⟩ := leaf_data hb
  have hbn : ∀ x, G.Adj b x → x=r := fun x hx ↦ (ha x hx).trans (ha r hrb.symm).symm
  have hodd := cubic_leaf_neighbors_odd hsmall hG hfail hrb.symm hbn hd
  obtain ⟨x,y,_,hrx,_,hx,_,_,_⟩ := NonbridgeCore.two_zero_nonbridge_neighbors T r hs hm hroot
  exact Nat.not_even_iff_odd.mpr (hodd x hrx) (QuotaParity.zero_quota_even T hx)

end Erdos583LeafCubicEvenDevelopment
