import Submission.CubicTriangleOddAttachment

/-! Connectivity of the cubic-pair deletion along its existing path carrier. -/
namespace Erdos583CubicTrianglePunctureDevelopment
open SimpleGraph Erdos583Work
open Erdos583CubicTriangleCarrierDevelopment Erdos583CubicTriangleOddAttachmentDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma punctured_carrier_reaches_root {V : Type*} {G : SimpleGraph V} {r x y a b : V}
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hyb : G.Adj y b)
    (hay : a ≠ y)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b)
    (P : G.Walk x y) (hP : P.IsPath) (hrP : r ∈ P.support)
    (hnrx : s(r,x) ∉ P.edges) (hnry : s(r,y) ∉ P.edges) (hnxy : s(x,y) ∉ P.edges)
    (hnab : s(a,b) ∉ P.edges) :
    (puncture (G.deleteEdges {s(a,b)}) ({x,y} : Set V)).Reachable r a ∧
      (puncture (G.deleteEdges {s(a,b)}) ({x,y} : Set V)).Reachable r b := by
  classical
  cases P with
  | nil => exact (hxy.ne rfl).elim
  | @cons _ c _ hxc Q =>
    have hca : c=a := by
      rcases hNx c hxc with h | h | h
      · subst c; exact (hnrx (by simp [Sym2.eq_swap])).elim
      · subst c; exact (hnxy (by simp)).elim
      · exact h
    subst c
    obtain ⟨d,R,hdy,hQR⟩ : ∃ d, ∃ R : G.Walk a d, ∃ hdy : G.Adj d y, Q=R.concat hdy := by
      cases Q with
      | nil => exact (hay rfl).elim
      | cons h A => exact Walk.exists_cons_eq_concat h A
    subst Q
    have hdb : d=b := by
      rcases hNy d hdy.symm with h | h | h
      · subst d; exact (hnry (by simp)).elim
      · subst d; exact (hnxy (by simp)).elim
      · exact h
    subst d
    have hRC := (Walk.cons_isPath_iff hxc (R.concat hdy)).mp hP
    have hRR := (Walk.concat_isPath_iff hdy).mp hRC.1
    have hrR : r ∈ R.support := by
      simpa only [Walk.support_cons,Walk.support_concat,List.concat_eq_append,List.mem_cons,List.mem_append,
        List.not_mem_nil,hrx.ne,hry.ne,false_or,or_false] using hrP
    have hxR : x ∉ R.support := fun hx ↦ hRC.2 (by
      simp only [Walk.support_concat,List.concat_eq_append,List.mem_append,List.mem_singleton]
      exact Or.inl hx)
    let K := puncture (G.deleteEdges {s(a,b)}) ({x,y} : Set V)
    have htransfer : ∀ e ∈ R.edges, e ∈ K.edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h u v =>
        refine ⟨deleteEdges_adj.mpr ⟨R.adj_of_mem_edges he,?_⟩,?_,?_⟩
        · intro heq
          exact hnab (by
            simp only [Walk.edges_cons,Walk.edges_concat,List.concat_eq_append,List.mem_cons,List.mem_append]
            exact Or.inr (Or.inl (heq ▸ he)))
        · have hu := R.fst_mem_support_of_mem_edges he
          rintro (rfl|rfl)
          · exact hxR hu
          · exact hRR.2 hu
        · have hv := R.snd_mem_support_of_mem_edges he
          rintro (rfl|rfl)
          · exact hxR hv
          · exact hRR.2 hv
    let A := R.transfer K htransfer
    have hrA : r ∈ A.support := by simpa only [A,Walk.support_transfer] using hrR
    exact ⟨(A.takeUntil r hrA).reachable.symm,(A.dropUntil r hrA).reachable⟩

lemma cubic_pair_puncture_delete_connected {V : Type*} {G : SimpleGraph V}
    (hG : SupportConnected G) {r x y a b : V}
    (hrx : G.Adj r x) (hry : G.Adj r y)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b)
    (hra : (puncture (G.deleteEdges {s(a,b)}) ({x,y} : Set V)).Reachable r a)
    (hrb : (puncture (G.deleteEdges {s(a,b)}) ({x,y} : Set V)).Reachable r b) :
    SupportConnected (puncture (G.deleteEdges {s(a,b)}) ({x,y} : Set V)) := by
  classical
  let S : Set V := {x,y}
  let K := puncture (G.deleteEdges {s(a,b)}) S
  let f (v : V) := if v ∈ S then r else v
  have hle : K ≤ G := (puncture_le _ _).trans (deleteEdges_le _)
  have hboundary {t z} (ht : t ∈ S) (hz : z ∉ S) (htz : G.Adj t z) : K.Reachable r z := by
    rcases ht with rfl | rfl
    · rcases hNx z htz with rfl | rfl | rfl
      · exact .rfl
      · exact (hz (Or.inr rfl)).elim
      · exact hra
    · rcases hNy z htz with rfl | rfl | rfl
      · exact .rfl
      · exact (hz (Or.inl rfl)).elim
      · exact hrb
  apply hG.of_reachable_map f (support_mono hle)
  · intro u v huv
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · simp only [f,if_pos hu,if_pos hv]; exact .rfl
    · simp only [f,if_pos hu,if_neg hv]; exact hboundary hu hv huv
    · simp only [f,if_neg hu,if_pos hv]; exact (hboundary hv hu huv.symm).symm
    · simp only [f,if_neg hu,if_neg hv]
      by_cases he : s(u,v)=s(a,b)
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hra.symm.trans hrb
        · exact hrb.symm.trans hra
      · exact (show K.Adj u v from ⟨deleteEdges_adj.mpr ⟨huv,he⟩,hu,hv⟩).reachable
  · intro u hu
    obtain ⟨v,hv⟩ := hu
    simp only [f,if_neg hv.2.1]
    exact .rfl

lemma cubic_triangle_odd_attachment_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected) {r x y a b : Fin n}
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hyb : G.Adj y b) (hab : G.Adj a b)
    (har : a ≠ r) (hay : a ≠ y) (hbr : b ≠ r) (hbx : b ≠ x)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b)
    (hrodd : Odd (Nat.card (G.neighborSet r))) (haodd : Odd (Nat.card (G.neighborSet a)))
    (P : G.Walk x y) (hP : P.IsPath) (hrP : r ∈ P.support)
    (hnrx : s(r,x) ∉ P.edges) (hnry : s(r,y) ∉ P.edges) (hnxy : s(x,y) ∉ P.edges)
    (hnab : s(a,b) ∉ P.edges) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  obtain ⟨hra,hrb⟩ := punctured_carrier_reaches_root hrx hry hxy hxa hyb hay hNx hNy P hP hrP hnrx hnry hnxy hnab
  let K := puncture (G.deleteEdges {s(a,b)}) ({x,y} : Set (Fin n))
  have hK : SupportConnected K := cubic_pair_puncture_delete_connected
    (fun u _ v _ ↦ hG.preconnected u v) hrx hry hNx hNy hra hrb
  have hle : K ≤ G := (puncture_le _ _).trans (deleteEdges_le _)
  have hsub : K.support ⊆ G.support \ {x,y} := by
    rintro u ⟨v,hv⟩
    exact ⟨⟨v,hle hv⟩,hv.2.1⟩
  have hpair : ({x,y} : Set (Fin n)) ⊆ G.support := by
    rintro u (rfl|rfl)
    · exact ⟨r,hrx.symm⟩
    · exact ⟨r,hry.symm⟩
  have hcard := support_card_bound_of_removed hpair hsub
  rw [Set.ncard_pair hxy.ne] at hcard
  have hGcard : G.support.ncard ≤ n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using G.support.ncard_le_card
  apply LowDegreeAdjacency.gallai_of_two_vertex_support_reduction hsmall G K hK (by omega)
  intro D hD
  exact cubic_triangle_odd_attachment_lift hrx hry hxy hxa hyb hab har hay hbr hbx hNx hNy hrodd haodd D hD

end Erdos583CubicTrianglePunctureDevelopment
