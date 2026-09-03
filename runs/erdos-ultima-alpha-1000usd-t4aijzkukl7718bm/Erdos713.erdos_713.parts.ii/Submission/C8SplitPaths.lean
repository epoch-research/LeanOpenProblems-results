import FormalConjecturesUtil
import Submission.RobustContractionWitnesses

/-! A nontrivial split of C8 has an exact eight-edge root path.
Thus robust contraction at an edge supplies a C9, not just an odd
cycle of length at most nine. No exponent comparison follows here. -/
open SimpleGraph Finset
namespace Erdos713C8SplitPaths
open Erdos713VertexSplitWitnesses Erdos713EdgeContraction
open Erdos713RobustContractionWitnesses
set_option maxHeartbeats 2000000

lemma adjacent_options : ∀ w x : Fin 8, (cycleGraph 8).Adj w x ↔
    x = w+1 ∨ x = w+7 := by
  simp only [cycleGraph_adj]
  decide

lemma forward_path (w : Fin 8) (S : Set (Fin 8))
    (hR : w+1 ∉ S) (hL : w+7 ∈ S) :
    ∃ p : (split (cycleGraph 8) w S).Walk none (some w), p.IsPath ∧ p.length = 8 := by
  have hR' : (split (cycleGraph 8) w S).Adj none (some (w+1)) := by
    exact ⟨(adjacent_options w _).mpr (by simp),hR⟩
  have h12 : (split (cycleGraph 8) w S).Adj (some (w+1)) (some (w+2)) := by
    refine ⟨?_,?_,?_⟩
    · rw [cycleGraph_adj]
      right
      abel
    · intro h
      have hh : (1 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
    · intro h
      have hh : (2 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
  have h23 : (split (cycleGraph 8) w S).Adj (some (w+2)) (some (w+3)) := by
    refine ⟨?_,?_,?_⟩
    · rw [cycleGraph_adj]
      right
      abel
    · intro h
      have hh : (2 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
    · intro h
      have hh : (3 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
  have h34 : (split (cycleGraph 8) w S).Adj (some (w+3)) (some (w+4)) := by
    refine ⟨?_,?_,?_⟩
    · rw [cycleGraph_adj]
      right
      abel
    · intro h
      have hh : (3 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
    · intro h
      have hh : (4 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
  have h45 : (split (cycleGraph 8) w S).Adj (some (w+4)) (some (w+5)) := by
    refine ⟨?_,?_,?_⟩
    · rw [cycleGraph_adj]
      right
      abel
    · intro h
      have hh : (4 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
    · intro h
      have hh : (5 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
  have h56 : (split (cycleGraph 8) w S).Adj (some (w+5)) (some (w+6)) := by
    refine ⟨?_,?_,?_⟩
    · rw [cycleGraph_adj]
      right
      abel
    · intro h
      have hh : (5 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
    · intro h
      have hh : (6 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
  have h67 : (split (cycleGraph 8) w S).Adj (some (w+6)) (some (w+7)) := by
    refine ⟨?_,?_,?_⟩
    · rw [cycleGraph_adj]
      right
      abel
    · intro h
      have hh : (6 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
    · intro h
      have hh : (7 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
  have hL' : (split (cycleGraph 8) w S).Adj (some (w+7)) (some w) := by
    refine ⟨((adjacent_options w _).mpr (by simp)).symm,?_,fun _ => hL⟩
    intro h
    have hh : (7 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
    exact absurd hh (by decide)
  let p : (split (cycleGraph 8) w S).Walk none (some w) :=
    Walk.cons hR' (Walk.cons h12 (Walk.cons h23 (Walk.cons h34 (Walk.cons h45 (Walk.cons h56 (Walk.cons h67 (Walk.cons hL' (Walk.nil))))))))
  refine ⟨p,?_,rfl⟩
  simp [p,Walk.isPath_def]

lemma backward_path (w : Fin 8) (S : Set (Fin 8))
    (hR : w+7 ∉ S) (hL : w+1 ∈ S) :
    ∃ p : (split (cycleGraph 8) w S).Walk none (some w), p.IsPath ∧ p.length = 8 := by
  have hR' : (split (cycleGraph 8) w S).Adj none (some (w+7)) := by
    exact ⟨(adjacent_options w _).mpr (by simp),hR⟩
  have h76 : (split (cycleGraph 8) w S).Adj (some (w+7)) (some (w+6)) := by
    refine ⟨?_,?_,?_⟩
    · rw [cycleGraph_adj]
      left
      abel
    · intro h
      have hh : (7 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
    · intro h
      have hh : (6 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
  have h65 : (split (cycleGraph 8) w S).Adj (some (w+6)) (some (w+5)) := by
    refine ⟨?_,?_,?_⟩
    · rw [cycleGraph_adj]
      left
      abel
    · intro h
      have hh : (6 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
    · intro h
      have hh : (5 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
  have h54 : (split (cycleGraph 8) w S).Adj (some (w+5)) (some (w+4)) := by
    refine ⟨?_,?_,?_⟩
    · rw [cycleGraph_adj]
      left
      abel
    · intro h
      have hh : (5 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
    · intro h
      have hh : (4 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
  have h43 : (split (cycleGraph 8) w S).Adj (some (w+4)) (some (w+3)) := by
    refine ⟨?_,?_,?_⟩
    · rw [cycleGraph_adj]
      left
      abel
    · intro h
      have hh : (4 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
    · intro h
      have hh : (3 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
  have h32 : (split (cycleGraph 8) w S).Adj (some (w+3)) (some (w+2)) := by
    refine ⟨?_,?_,?_⟩
    · rw [cycleGraph_adj]
      left
      abel
    · intro h
      have hh : (3 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
    · intro h
      have hh : (2 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
  have h21 : (split (cycleGraph 8) w S).Adj (some (w+2)) (some (w+1)) := by
    refine ⟨?_,?_,?_⟩
    · rw [cycleGraph_adj]
      left
      abel
    · intro h
      have hh : (2 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
    · intro h
      have hh : (1 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
      exact absurd hh (by decide)
  have hL' : (split (cycleGraph 8) w S).Adj (some (w+1)) (some w) := by
    refine ⟨((adjacent_options w _).mpr (by simp)).symm,?_,fun _ => hL⟩
    intro h
    have hh : (1 : Fin 8) = 0 := add_left_cancel (h.trans (add_zero w).symm)
    exact absurd hh (by decide)
  let p : (split (cycleGraph 8) w S).Walk none (some w) :=
    Walk.cons hR' (Walk.cons h76 (Walk.cons h65 (Walk.cons h54 (Walk.cons h43 (Walk.cons h32 (Walk.cons h21 (Walk.cons hL' (Walk.nil))))))))
  refine ⟨p,?_,rfl⟩
  simp [p,Walk.isPath_def]

lemma split_has_path_eight (w : Fin 8) (S : Set (Fin 8))
    (hL : ∃ x, (cycleGraph 8).Adj w x ∧ x ∈ S)
    (hR : ∃ y, (cycleGraph 8).Adj w y ∧ y ∉ S) :
    ∃ p : (split (cycleGraph 8) w S).Walk none (some w), p.IsPath ∧ p.length = 8 := by
  obtain ⟨x,hx,hxS⟩ := hL
  obtain ⟨y,hy,hyS⟩ := hR
  rcases (adjacent_options w x).mp hx with rfl | rfl <;>
    rcases (adjacent_options w y).mp hy with rfl | rfl
  · exact (hyS hxS).elim
  · exact backward_path w S hyS hxS
  · exact forward_path w S hyS hxS
  · exact (hyS hxS).elim

/-- Contracting an edge after arbitrary small edge deletions gives an
actual nine-cycle. Only its distinguished root edge may belong to T. -/
theorem nine_cycle_after_deleting {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hf : (cycleGraph 8).Free G)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) (cycleGraph 8))
    {u v : V} (huv : G.Adj u v) (T : Finset (Sym2 V))
    (hsmall : (T.card : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ)+1 <
      (extremalNumber (Fintype.card V) (cycleGraph 8) : ℝ)-
        (extremalNumber (Fintype.card V-1) (cycleGraph 8) : ℝ)) :
    ∃ p : G.Walk u u, p.IsCycle ∧ p.length = 9 ∧ s(u,v) ∈ p.edges ∧
      ∀ e ∈ p.edges, e ≠ s(u,v) → e ∉ T := by
  classical
  obtain ⟨w,S,f,hu,hv,hL,hR⟩ := split_after_deleting (cycleGraph 8) G hf he huv.ne T hsmall
  obtain ⟨p,hp,hLen⟩ := split_has_path_eight w S hL hR
  let K := eraseEdge (G.deleteEdges (T : Set (Sym2 V))) u v
  have hle : K ≤ G := (eraseEdge_le _ u v).trans (G.deleteEdges_le _)
  let p0 : K.Walk v u := (p.map f.toHom).copy hv hu
  have hp0 : p0.IsPath :=
    (Walk.isPath_copy _ hv hu).mpr (Walk.map_isPath_of_injective f.injective hp)
  have hlen0 : p0.length = 8 := by simpa only [p0,Walk.length_copy,Walk.length_map] using hLen
  let pG : G.Walk v u := p0.mapLe hle
  have hpG : pG.IsPath := hp0.mapLe hle
  have hlenG : pG.length = 8 := by simpa [pG] using hlen0
  have hAvoid : ∀ e ∈ pG.edges, e ≠ s(u,v) ∧ e ∉ T := by
    intro e he
    have he0 : e ∈ p0.edges := by simpa only [pG,Walk.edges_mapLe_eq_edges] using he
    have heK := p0.edges_subset_edgeSet he0
    induction e using Sym2.ind with | _ x y =>
    have ha : K.Adj x y := by simpa using heK
    have ha' := deleteEdges_adj.mp ha
    exact ⟨ha'.2,(deleteEdges_adj.mp ha'.1).2⟩
  have hRoot : s(u,v) ∉ pG.edges := fun h => (hAvoid _ h).1 rfl
  refine ⟨Walk.cons huv pG,(Walk.cons_isCycle_iff pG huv).mpr ⟨hpG,hRoot⟩,?_,?_,?_⟩
  · simp only [Walk.length_cons,hlenG]
  · simp only [Walk.edges_cons,List.mem_cons,true_or]
  · intro e he hne
    have he' : e = s(u,v) ∨ e ∈ pG.edges := by simpa only [Walk.edges_cons,List.mem_cons] using he
    exact (hAvoid _ (he'.resolve_left hne)).2

#print axioms nine_cycle_after_deleting
#print axioms split_has_path_eight
end Erdos713C8SplitPaths
