import FormalConjecturesUtil
import Submission.VertexSplitWitnesses

/-! A nontrivial split of a bipartite graph has a short even root path
when deletion of the split vertex leaves a preconnected graph. -/
open SimpleGraph
namespace Erdos713SplitRootPaths
open Erdos713VertexSplitWitnesses
variable {W : Type*}
set_option maxHeartbeats 2000000

lemma even_root_path [Fintype W] {H : SimpleGraph W} (hH : H.IsBipartite)
    (w : W) (hRest : (H.induce {w}ᶜ).Preconnected) (S : Set W)
    (hLeft : ∃ x, H.Adj w x ∧ x ∈ S) (hRight : ∃ y, H.Adj w y ∧ y ∉ S) :
    ∃ p : (Erdos713VertexSplitWitnesses.split H w S).Walk none (some w),
      p.IsPath ∧ Even p.length ∧ p.length ≤ Fintype.card W := by
  classical
  obtain ⟨x,hx,hxS⟩ := hLeft
  obtain ⟨y,hy,hyS⟩ := hRight
  let x' : ({w}ᶜ : Set W) := ⟨x,hx.ne.symm⟩
  let y' : ({w}ᶜ : Set W) := ⟨y,hy.ne.symm⟩
  let inc : H.induce {w}ᶜ →g Erdos713VertexSplitWitnesses.split H w S :=
    ⟨fun z => some z.val,by
      intro z t hzt
      exact ⟨hzt,fun h => (z.property h).elim,fun h => (t.property h).elim⟩⟩
  have hL : (Erdos713VertexSplitWitnesses.split H w S).Adj (some w) (some x) :=
    ⟨hx,fun _ => hxS,fun h => (hx.ne h.symm).elim⟩
  have hR : (Erdos713VertexSplitWitnesses.split H w S).Adj none (some y) := ⟨hy,hyS⟩
  have hm : (Erdos713VertexSplitWitnesses.split H w S).Reachable (some y) (some x) :=
    (hRest y' x').map inc
  obtain ⟨p,hp⟩ := (hR.reachable.trans (hm.trans hL.symm.reachable)).exists_isPath
  have hEven := (two_colorable_iff_forall_loop_even.mp hH) w (p.map (projectHom H w S))
  have hLength := hp.length_lt
  simp only [Fintype.card_option] at hLength
  refine ⟨p,hp,?_,by omega⟩
  simpa only [Walk.length_map] using hEven

#print axioms even_root_path
end Erdos713SplitRootPaths
