import Submission.FanCycleAbsorption

/-! A necessary obstruction in a maximal endpoint packing: every unused-cycle
vertex has two escaping neighboring endpoints whose packed paths meet elsewhere.
No terminating augmentation follows just from this obstruction. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 1000000
variable {V : Type*} {G : SimpleGraph V}

namespace FanAbsorption
lemma cycle_as_rim {v : V} (C : G.Walk v v) (hC : C.IsCycle) :
    ∃ (x y : V) (Q : G.Walk x y) (hx : G.Adj v x) (hy : G.Adj y v),
      C = Walk.cons hx (Q.concat hy) ∧ x ≠ y := by
  cases C with
  | nil => exact (hC.ne_nil rfl).elim
  | @cons v x v hx P =>
    cases P with
    | nil => exact (hx.ne rfl).elim
    | @cons x w v hxw P =>
      obtain ⟨y,Q,hy,he⟩ := Walk.exists_cons_eq_concat hxw P
      refine ⟨x,y,Q,hx,hy,by rw [he],?_⟩
      have hC' : (Walk.cons hx (Q.concat hy)).IsCycle := by rwa [he] at hC
      have hQ : Q.IsPath := (Walk.concat_isPath_iff hy).mp
        ((Walk.cons_isCycle_iff (Q.concat hy) hx).mp hC').1 |>.1
      intro hxy
      cases hxy
      have hnil := (Walk.isPath_iff_eq_nil Q).mp hQ
      have hl := hC'.three_le_length
      simp only [hnil,Walk.length_cons,Walk.length_concat,Walk.length_nil] at hl
      omega
end FanAbsorption

variable [Fintype V]

lemma Maximal.unused_cycle_escaping_paths_meet {L : List (Piece G)} (hL : Maximal L)
    {a v : V} (C : G.Walk a a) (hC : C.IsCycle) (hv : v ∈ C.support)
    (hunused : (edgeList L).Disjoint C.edges) :
    ∃ (t z w : V) (p q : Piece G), t ≠ z ∧ G.Adj v t ∧ G.Adj v z ∧
      p ∈ L ∧ q ∈ L ∧ (t = p.src ∨ t = p.dst) ∧ (z = q.src ∨ z = q.dst) ∧
      v ∉ p.walk.support ∧ v ∉ q.walk.support ∧ w ≠ v ∧
      w ∈ p.walk.support ∧ w ∈ q.walk.support := by
  let R := C.rotate hv
  have hR : R.IsCycle := hC.rotate hv
  have hRe : R.edges.Perm C.edges := (C.rotate_edges hv).perm
  have hdisR : (edgeList L).Disjoint R.edges := by
    intro e he heR
    exact hunused he (hRe.mem_iff.mp heR)
  obtain ⟨x,y,Q,hx,hy,heq,hxy⟩ := FanAbsorption.cycle_as_rim R hR
  have hQcy : (Walk.cons hx (Q.concat hy)).IsCycle := heq ▸ hR
  have hdisQ : (edgeList L).Disjoint (Walk.cons hx (Q.concat hy)).edges := heq ▸ hdisR
  have hxu : (G \ coveredGraph L).Adj v x := by
    refine ⟨hx,?_⟩
    intro h
    exact hdisQ ((coveredGraph_adj L v x).mp h) (by simp)
  have hyu : (G \ coveredGraph L).Adj v y := by
    refine ⟨hy.symm,?_⟩
    intro h
    apply hdisQ ((coveredGraph_adj L v y).mp h)
    simp [Walk.edges_concat,Sym2.eq_swap]
  obtain ⟨t,z,M,htz,hvt,hvz,ht,hz,_,hME,hMV,hkeep⟩ := hL.1.rotate_two_endpoint_fans hxu hyu hxy
  obtain ⟨p,hp,hpt,hpv⟩ := hL.1.endpoint_path_avoids_of_not_touching ht
  obtain ⟨q,hq,hqz,hqv⟩ := hL.1.endpoint_path_avoids_of_not_touching hz
  have hnot : ¬ p.walk.support.Disjoint q.walk.support := by
    intro hdis
    exact FanAbsorption.no_disjoint_terminal_paths hL Q hx hy hQcy hdisQ hME hMV hvt hvz
      p q (hkeep p hp hpv) (hkeep q hq hqv) hpt hqz hpv hqv hdis
  have hmeet : ∃ w, w ∈ p.walk.support ∧ w ∈ q.walk.support := by
    by_contra! hn
    apply hnot
    intro w hw hqw
    exact hn w hw hqw
  obtain ⟨w,hwp,hwq⟩ := hmeet
  have hwv : w ≠ v := by rintro rfl; exact hpv hwp
  exact ⟨t,z,w,p,q,htz,hvt,hvz,hp,hq,hpt,hqz,hpv,hqv,hwv,hwp,hwq⟩

end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.Maximal.unused_cycle_escaping_paths_meet
