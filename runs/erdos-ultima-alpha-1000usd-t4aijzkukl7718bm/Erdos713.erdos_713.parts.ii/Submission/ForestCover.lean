import FormalConjecturesUtil
import Submission.OrientedCloneC8

/-! A locally injective homomorphism into a forest has an acyclic domain. -/
open SimpleGraph
namespace Erdos713ForestCover
open Erdos713OrientedCloneC8
set_option maxHeartbeats 2000000
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

lemma map_edges_chain (f : G →g H)
    (hf : ∀ u v w, G.Adj u v → G.Adj u w → f v = f w → v = w)
    {u v : V} (p : G.Walk u v) (hp : p.edges.IsChain (· ≠ ·)) :
    (p.map f).edges.IsChain (· ≠ ·) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    cases p with
    | nil => simp
    | @cons _ z _ h' p =>
      have hp' := List.isChain_cons_cons.mp hp
      have he : s(f u,f v) ≠ s(f v,f z) := by
        intro he
        rcases Sym2.eq_iff.mp he with he|he
        · exact (f.map_rel h).ne he.1
        · have hu : u = z := hf v u z h.symm h' he.1
          exact hp'.1 (by simp [hu,Sym2.eq_swap])
      exact List.isChain_cons_cons.mpr ⟨he,ih hp'.2⟩

theorem acyclic_of_locally_injective (f : G →g H) (hH : H.IsAcyclic)
    (hf : ∀ u v w, G.Adj u v → G.Adj u w → f v = f w → v = w) : G.IsAcyclic := by
  intro u p hp
  have hc := map_edges_chain f hf p hp.isCircuit.isTrail.edges_nodup.isChain
  have hh := (hH.isPath_iff_isChain (p.map f)).mpr hc
  have he := (p.map f).isPath_iff_eq_nil.mp hh
  have hl := congrArg Walk.length he
  simp only [Walk.length_map,Walk.length_nil] at hl
  have hp3 := hp.three_le_length
  omega

/-- The bipartite double cover of a forest is again a forest. -/
theorem double_cover_acyclic (hG : G.IsAcyclic) :
    (graph (⊥ : SimpleGraph V) G.Adj).IsAcyclic := by
  let f : graph (⊥ : SimpleGraph V) G.Adj →g G := ⟨root,by
    rintro (u|u) (v|v) h
    · exact h.elim
    · exact (show G.Adj v u from h).symm
    · exact h
    · exact h.elim⟩
  apply acyclic_of_locally_injective f hG
  rintro (u|u) (v|v) (w|w) huv huw he
  all_goals simp only [graph,bot_adj] at huv huw
  all_goals change v = w at he
  all_goals first | exact congrArg Sum.inl he | exact congrArg Sum.inr he

#print axioms acyclic_of_locally_injective
#print axioms double_cover_acyclic
end Erdos713ForestCover
