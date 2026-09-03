import Submission.ShortTriangleIncidence

/-! A fresh-shortcut reduction at two cubic vertices of a triangle. -/
namespace Erdos583CubicTriangleReductionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.LollipopEar
open Erdos583ShortTriangleIncidenceDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma cubic_triangle_fresh_shortcut {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : SupportConnected G) {r x y a b : V}
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hyb : G.Adj y b)
    (har : a ≠ r) (hay : a ≠ y) (hbr : b ≠ r) (hbx : b ≠ x)
    (hab : a ≠ b) (hnab : ¬G.Adj a b)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b)
    (hreach : (puncture G ({x,y} : Set V)).Reachable a r) :
    ∃ H : SimpleGraph V, SupportConnected H ∧ H.support.ncard+2 ≤ G.support.ncard ∧
      ∀ D : Finset H.Subgraph, GoodDecomposition H D →
        ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  classical
  let S : Set V := {x,y}
  let H := puncture G S ⊔ edge a b
  have haS : a ∉ S := by simp [S,hxa.ne.symm,hay]
  have hbS : b ∉ S := by simp [S,hbx,hyb.ne.symm]
  have has : a ∈ G.support := ⟨x,hxa.symm⟩
  have hbs : b ∈ G.support := ⟨y,hyb.symm⟩
  have hxS : x ∈ G.support := ⟨r,hrx.symm⟩
  have hyS : y ∈ G.support := ⟨r,hry.symm⟩
  have habH : H.Adj a b := Or.inr ((edge_adj a b a b).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab⟩)
  refine ⟨H,?_,?_,?_⟩
  · apply hG.puncture_add_edge S hab haS has hbs
    intro t ht z hz htz
    have hz' : z=r ∨ z=a ∨ z=b := by
      rcases ht with rfl | rfl
      · rcases hNx z htz with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact (hz (Or.inr rfl)).elim
        · exact Or.inr (Or.inl rfl)
      · rcases hNy z htz with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact (hz (Or.inl rfl)).elim
        · exact Or.inr (Or.inr rfl)
    rcases hz' with rfl | rfl | rfl
    · exact hreach.mono le_sup_left
    · exact .rfl
    · exact habH.reachable
  · have hh := support_card_puncture_add_edge (T := S) (R := S) has hbs
      (by rintro z (rfl|rfl) <;> assumption) (fun _ h ↦ h) haS hbS
    simpa only [S,Set.ncard_pair hxy.ne] using hh
  · intro D hD
    let P : G.Walk a b := Walk.cons hxa.symm (Walk.cons hxy (Walk.cons hyb Walk.nil))
    let Q : G.Walk x y := Walk.cons hrx.symm (Walk.cons hry Walk.nil)
    have hP : P.IsPath := by
      apply Walk.IsPath.mk'
      simp [P,Walk.support,hxa.ne.symm,hay,hab,hxy.ne,hbx.symm,hyb.ne]
    have hQ : Q.IsPath := by
      apply Walk.IsPath.mk'
      simp [Q,Walk.support,hrx.ne.symm,hxy.ne,hry.ne]
    apply hD.puncture_expand_restore S hab (fun h ↦ hnab h.1) P hP Q hQ
    · intro z hz hza hzb
      simp only [P,Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact (hza rfl).elim
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact (hzb rfl).elim
    · intro t ht z htz
      rcases ht with rfl | rfl
      · rcases hNx z htz with rfl | rfl | rfl <;> simp [P,Q,Sym2.eq_swap]
      · rcases hNy z htz with rfl | rfl | rfl <;> simp [P,Q,Sym2.eq_swap]
    · intro e he
      have he' : e=s(x,r) ∨ e=s(r,y) := by simpa [Q] using he
      rcases he' with rfl | rfl
      · exact ⟨x,Or.inl rfl,by simp⟩
      · exact ⟨y,Or.inr rfl,by simp⟩
    · simp [P,Q,hrx.ne.symm,hry.ne.symm,hxy.ne,hxy.ne.symm,
        hxa.ne.symm,hyb.ne.symm,har,hay,hbr,hbx]

lemma failure_cubic_triangle_external_adj {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {r x y a b : Fin n}
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hyb : G.Adj y b)
    (har : a ≠ r) (hay : a ≠ y) (hbr : b ≠ r) (hbx : b ≠ x) (hab : a ≠ b)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=b)
    (hreach : (puncture G ({x,y} : Set (Fin n))).Reachable a r) : G.Adj a b := by
  by_contra hnab
  obtain ⟨H,hH,hc,hlift⟩ := cubic_triangle_fresh_shortcut G
    (fun u _ v _ ↦ hG.preconnected u v) hrx hry hxy hxa hyb har hay hbr hbx hab hnab hNx hNy hreach
  have hcard : G.support.ncard ≤ n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using G.support.ncard_le_card
  exact hfail (LowDegreeAdjacency.gallai_of_two_vertex_support_reduction hsmall G H hH (by omega) hlift)

end Erdos583CubicTriangleReductionDevelopment
