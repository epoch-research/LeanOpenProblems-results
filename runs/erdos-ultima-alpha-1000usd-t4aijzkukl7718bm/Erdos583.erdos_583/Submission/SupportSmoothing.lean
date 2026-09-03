import Submission.RestoreTriangle

/-! Suppressing a degree-two vertex on connected support, without degree bounds elsewhere. -/
namespace Erdos583SupportSmoothingDevelopment
open SimpleGraph Erdos583Work
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

noncomputable def smooth {V : Type*} (G : SimpleGraph V) (x a b : V) : SimpleGraph V :=
  puncture G ({x} : Set V) ⊔ edge a b

lemma smooth_support_connected {V : Type*} {G : SimpleGraph V}
    (hG : SupportConnected G) {x a b : V}
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : a ≠ b)
    (hNx : ∀ z, G.Adj x z → z=a ∨ z=b) : SupportConnected (smooth G x a b) := by
  apply hG.puncture_add_edge ({x} : Set V) hab hxa.ne.symm ⟨x,hxa.symm⟩ ⟨x,hxb.symm⟩
  intro t ht z _ htz
  have htx : t=x := ht
  subst t
  rcases hNx z htz with h | h
  · subst z; exact .rfl
  · subst z
    exact (show (smooth G x a b).Adj a b from
      Or.inr ((edge_adj a b a b).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab⟩)).reachable

lemma smooth_support_card {V : Type*} [Fintype V] {G : SimpleGraph V} {x a b : V}
    (hxa : G.Adj x a) (hxb : G.Adj x b) :
    (smooth G x a b).support.ncard+1 ≤ G.support.ncard := by
  have hh := support_card_puncture_add_edge (T := ({x} : Set V)) (R := ({x} : Set V))
    (a := a) (b := b) ⟨x,hxa.symm⟩ ⟨x,hxb.symm⟩
    (by rintro z rfl; exact ⟨a,hxa⟩) (fun _ h ↦ h) hxa.ne.symm hxb.ne.symm
  simpa only [smooth,Set.ncard_singleton] using hh

lemma smooth_neighborSet {V : Type*} {G : SimpleGraph V} {x a b y : V}
    (hyx : y ≠ x) (hya : y ≠ a) (hyb : y ≠ b) (hnxy : ¬G.Adj x y) :
    (smooth G x a b).neighborSet y=G.neighborSet y := by
  ext z
  simp only [mem_neighborSet,smooth,sup_adj,puncture_adj,Set.mem_singleton_iff,edge_adj]
  constructor
  · rintro (⟨h,_,_⟩|⟨(⟨h,_⟩|⟨h,_⟩),_⟩)
    · exact h
    · exact (hya h).elim
    · exact (hyb h).elim
  · intro h
    exact Or.inl ⟨h,hyx,fun hz ↦ hnxy (hz ▸ h.symm)⟩

lemma smooth_lift {V : Type*} [Fintype V] {G : SimpleGraph V} {x a b : V}
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : a ≠ b)
    (hNx : ∀ z, G.Adj x z → z=a ∨ z=b) (hnab : ¬G.Adj a b)
    (D : Finset (smooth G x a b).Subgraph) (hD : GoodDecomposition (smooth G x a b) D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card := by
  classical
  let R : G.Walk a b := Walk.cons hxa.symm (Walk.cons hxb Walk.nil)
  have hR : R.IsPath := by simp [R,Walk.cons_isPath_iff,hxa.ne.symm,hxb.ne,hab]
  have hdiff : (smooth G x a b).edgeSet \ {s(a,b)}=(puncture G ({x} : Set V)).edgeSet :=
    edgeSet_sup_edge_diff _ hab (fun h ↦ hnab h.1)
  have hcover : G.edgeSet=((smooth G x a b).edgeSet \ {s(a,b)}) ∪ R.toSubgraph.edgeSet := by
    rw [hdiff]
    have hh := puncture_two_walks_cover ({x} : Set V) R (Walk.nil (u := x) (G := G)) (by
      intro t ht z htz
      have htx : t=x := ht
      subst t
      rcases hNx z htz with rfl | rfl <;> simp [R,Sym2.eq_swap])
    simpa using hh
  apply hD.expand_edge (a := a) (b := b)
    (Or.inr ((edge_adj a b a b).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab⟩)) R hR _ hcover
  intro z hz hza hzb
  have hzx : z=x := by simpa [R,Walk.support,hza,hzb] using hz
  exact puncture_fresh_internal (T := ({x} : Set V)) hzx hza hzb

end Erdos583SupportSmoothingDevelopment
