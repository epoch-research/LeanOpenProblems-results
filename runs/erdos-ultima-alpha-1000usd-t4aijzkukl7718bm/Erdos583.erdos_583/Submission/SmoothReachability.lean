import Submission.TwoComponentBudget

/-! Support and reachability under degree-two smoothing, including disconnected graphs. -/
namespace Erdos583SmoothReachabilityDevelopment
open SimpleGraph Erdos583Work
open Erdos583SupportSmoothingDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma smooth_support_eq {V : Type*} {G : SimpleGraph V} {x a b : V}
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : a ≠ b)
    (hNx : ∀ z, G.Adj x z → z=a ∨ z=b) :
    (smooth G x a b).support=G.support \ {x} := by
  have habH : (smooth G x a b).Adj a b :=
    Or.inr ((edge_adj a b a b).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab⟩)
  ext v
  constructor
  · rintro ⟨w,hw⟩
    rcases hw with hw | hw
    · exact ⟨⟨w,hw.1⟩,hw.2.1⟩
    · obtain ⟨hw,_⟩ := (edge_adj a b v w).mp hw
      rcases hw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨⟨x,hxa.symm⟩,hxa.ne.symm⟩
      · exact ⟨⟨x,hxb.symm⟩,hxb.ne.symm⟩
  · rintro ⟨⟨w,hw⟩,hv⟩
    by_cases hwx : w=x
    · subst w
      rcases hNx v hw.symm with rfl | rfl
      · exact ⟨b,habH⟩
      · exact ⟨a,habH.symm⟩
    · exact ⟨w,Or.inl ⟨hw,hv,hwx⟩⟩

lemma smooth_reachable_forward {V : Type*} {G : SimpleGraph V} {x a b u v : V}
    (hab : a ≠ b) (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hNx : ∀ z, G.Adj x z → z=a ∨ z=b)
    (hux : u ≠ x) (hvx : v ≠ x) (h : G.Reachable u v) :
    (smooth G x a b).Reachable u v := by
  classical
  let H := smooth G x a b
  let f (t : V) := if t=x then a else t
  have habH : H.Adj a b := Or.inr ((edge_adj a b a b).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab⟩)
  have hedge (s t : V) (hst : G.Adj s t) : H.Reachable (f s) (f t) := by
    by_cases hs : s=x
    · subst s
      have ht : t ≠ x := hst.ne.symm
      simp only [f,if_pos rfl,if_neg ht]
      rcases hNx t hst with rfl | rfl
      · exact .rfl
      · exact habH.reachable
    by_cases ht : t=x
    · subst t
      simp only [f,if_pos rfl,if_neg hs]
      rcases hNx s hst.symm with rfl | rfl
      · exact .rfl
      · exact habH.symm.reachable
    simp only [f,if_neg hs,if_neg ht]
    exact (show H.Adj s t from Or.inl ⟨hst,hs,ht⟩).reachable
  simpa only [f,if_neg hux,if_neg hvx] using reachable_map_to_reachable f hedge h

lemma smooth_reachable_backward {V : Type*} {G : SimpleGraph V} {x a b u v : V}
    (hxa : G.Adj x a) (hxb : G.Adj x b)
    (h : (smooth G x a b).Reachable u v) : G.Reachable u v := by
  apply reachable_map_to_reachable id _ h
  intro s t hst
  rcases hst with hh | hh
  · exact hh.1.reachable
  · obtain ⟨hh,_⟩ := (edge_adj a b s t).mp hh
    rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hxa.symm.reachable.trans hxb.reachable
    · exact hxb.symm.reachable.trans hxa.reachable

lemma puncture_shortcut_two_reachable {V : Type*} {G : SimpleGraph V}
    (hG : SupportConnected G) {x a b : V} (hxa : G.Adj x a)
    (hNx : ∀ z, G.Adj x z → z=a ∨ z=b) :
    let F := puncture (G.deleteEdges {s(a,b)}) ({x} : Set V)
    ∀ v ∈ F.support, F.Reachable a v ∨ F.Reachable b v := by
  classical
  let F := puncture (G.deleteEdges {s(a,b)}) ({x} : Set V)
  let S : Set V := {t | t=x ∨ F.Reachable a t ∨ F.Reachable b t}
  have hs : G.support ⊆ S := by
    apply hG.support_subset_of_closed ⟨a,hxa⟩ (show x ∈ S from Or.inl rfl)
    intro u hu v huv
    by_cases hv : v=x
    · exact Or.inl hv
    rcases hu with hu | hu | hu
    · subst u
      rcases hNx v huv with rfl | rfl
      · exact Or.inr (Or.inl .rfl)
      · exact Or.inr (Or.inr .rfl)
    · by_cases hux : u=x
      · subst u
        rcases hNx v huv with rfl | rfl
        · exact Or.inr (Or.inl .rfl)
        · exact Or.inr (Or.inr .rfl)
      by_cases he : s(u,v)=s(a,b)
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inr (Or.inr .rfl)
        · exact Or.inr (Or.inl .rfl)
      · exact Or.inr (Or.inl (hu.trans (show F.Adj u v from
          ⟨deleteEdges_adj.mpr ⟨huv,he⟩,hux,hv⟩).reachable))
    · by_cases hux : u=x
      · subst u
        rcases hNx v huv with rfl | rfl
        · exact Or.inr (Or.inl .rfl)
        · exact Or.inr (Or.inr .rfl)
      by_cases he : s(u,v)=s(a,b)
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inr (Or.inr .rfl)
        · exact Or.inr (Or.inl .rfl)
      · exact Or.inr (Or.inr (hu.trans (show F.Adj u v from
          ⟨deleteEdges_adj.mpr ⟨huv,he⟩,hux,hv⟩).reachable))
  change ∀ v ∈ F.support, F.Reachable a v ∨ F.Reachable b v
  intro v hv
  obtain ⟨w,hw⟩ := hv
  exact (hs ⟨w,deleteEdges_le _ hw.1⟩).resolve_left hw.2.1

end Erdos583SmoothReachabilityDevelopment
