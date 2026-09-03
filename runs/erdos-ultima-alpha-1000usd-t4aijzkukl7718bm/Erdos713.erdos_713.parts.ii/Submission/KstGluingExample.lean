import FormalConjecturesUtil
import Submission.CompactAssembly

/-! A concrete nine-vertex graph covered by the new gluing result.
This is an example of the completed family, not a counterexample to Erdos 713. -/
open SimpleGraph
namespace Erdos713Assembly
open Erdos713Gluing

abbrev OppositeVertex := Erdos713Gluing.Vertex
  (Sum.inl 0 : Fin 2 ⊕ Fin 3) (Sum.inr 0 : Fin 2 ⊕ Fin 3)

local instance : DecidableRel oppositeK23.Adj := by
  rintro (a | a) (b | b) <;>
    dsimp [oppositeK23,wedge,Erdos713K2t.K2t,completeBipartiteGraph] <;> infer_instance

lemma oppositeK23_card : Fintype.card OppositeVertex = 9 := by decide

lemma oppositeK23_min_degree : ∀ v, 2 ≤ oppositeK23.degree v := by decide

lemma oppositeK23_connected : oppositeK23.Connected := by
  let x : OppositeVertex := Sum.inl (Sum.inl 0)
  have hNear : ∀ v, v = x ∨ oppositeK23.Adj v x ∨
      ∃ w, oppositeK23.Adj v w ∧ oppositeK23.Adj w x := by decide
  have hr (v : OppositeVertex) : oppositeK23.Reachable v x := by
    rcases hNear v with rfl | hv | ⟨w,hvw,hwx⟩
    · exact Reachable.refl _
    · exact hv.reachable
    · exact hvw.reachable.trans hwx.reachable
  exact ⟨fun u v => (hr u).trans (hr v).symm⟩

def oppositeSide : Finset OppositeVertex := Finset.univ.filter
  (fun v => v.elim Sum.isLeft (fun w => w.val.isRight))

lemma oppositeSide_card : oppositeSide.card = 4 := by decide

set_option synthInstance.maxSize 2048 in
lemma oppositeK23_bipartiteWith : oppositeK23.IsBipartiteWith
    (oppositeSide : Set OppositeVertex) (oppositeSide : Set OppositeVertex)ᶜ := by
  have hh : ∀ u v, oppositeK23.Adj u v →
      (u ∈ oppositeSide ∧ v ∉ oppositeSide) ∨ (u ∉ oppositeSide ∧ v ∈ oppositeSide) := by decide
  exact ⟨disjoint_compl_right,hh⟩


set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma oppositeK23_side_card (S : Set OppositeVertex)
    (hS : oppositeK23.IsBipartiteWith S Sᶜ) : 4 ≤ Nat.card S := by
  have hfinite : ∀ T : Finset OppositeVertex,
      (∀ u v, oppositeK23.Adj u v → (u ∈ T ↔ v ∉ T)) → 4 ≤ T.card := by decide
  classical
  have hh := hfinite S.toFinset (by
    intro u v huv
    simp only [Set.mem_toFinset]
    constructor
    · exact fun hu => hS.mem_of_mem_adj hu huv
    · intro hv
      exact (hS.mem_of_adj huv).resolve_right (fun hh => hv hh.2) |>.1)
  simpa only [Set.toFinset_card,Set.ncard_eq_toFinset_card, Nat.card_eq_fintype_card] using hh

#print axioms oppositeK23_bipartiteWith
#print axioms oppositeK23_min_degree
#print axioms oppositeK23_connected
#print axioms oppositeK23_side_card
end Erdos713Assembly
