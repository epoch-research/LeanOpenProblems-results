import Submission.ShortTriangleQuarticPairExclusion

/-! Removing a leaf from connected support, with its edge and support count tracked. -/
namespace Erdos583LeafPunctureDevelopment
open SimpleGraph Erdos583Work
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma puncture_leaf_connected {V : Type*} {G : SimpleGraph V}
    (hG : SupportConnected G) {y c : V} (hNy : ∀ v, G.Adj y v → v=c) :
    SupportConnected (puncture G ({y} : Set V)) := by
  classical
  let F := puncture G ({y} : Set V)
  let f (v : V) := if v=y then c else v
  apply hG.of_reachable_map f (support_mono (puncture_le G {y}))
  · intro u v huv
    by_cases hu : u=y
    · subst u
      have hv : v ≠ y := huv.ne.symm
      simp only [f,if_pos rfl,if_neg hv]
      rw [hNy v huv]
    by_cases hv : v=y
    · subst v
      simp only [f,if_neg hu,if_pos rfl]
      rw [hNy u huv.symm]
    simp only [f,if_neg hu,if_neg hv]
    exact (show F.Adj u v from ⟨huv,hu,hv⟩).reachable
  · rintro u ⟨v,hv⟩
    have hu : u ≠ y := hv.2.1
    simp only [f,if_neg hu]
    exact .rfl

lemma puncture_leaf_edgeSet {V : Type*} {G : SimpleGraph V} {y c : V}
    (hyc : G.Adj y c) (hNy : ∀ v, G.Adj y v → v=c) :
    G.edgeSet=(puncture G ({y} : Set V)).edgeSet ∪ {s(y,c)} := by
  ext e
  induction e using Sym2.ind with
  | h u v =>
    constructor
    · intro huv
      by_cases hu : u=y
      · subst u; rw [hNy v huv]; exact Or.inr rfl
      by_cases hv : v=y
      · subst v; rw [hNy u huv.symm]; exact Or.inr Sym2.eq_swap
      · exact Or.inl ⟨huv,hu,hv⟩
    · rintro (h|h)
      · exact h.1
      · exact (G.adj_congr_of_sym2 h).mpr hyc

lemma puncture_supported_vertex_card {V : Type*} [Fintype V] {G : SimpleGraph V} {y : V}
    (hy : y ∈ G.support) : (puncture G ({y} : Set V)).support.ncard+1 ≤ G.support.ncard := by
  have hh := support_card_bound_of_removed (R := ({y} : Set V))
    (by rintro v rfl; exact hy)
    (show (puncture G ({y} : Set V)).support ⊆ G.support \ {y} from by
      rintro v ⟨w,hw⟩; exact ⟨⟨w,hw.1⟩,hw.2.1⟩)
  simpa only [Set.ncard_singleton] using hh

end Erdos583LeafPunctureDevelopment
