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


#synth Decidable (∀ T : Finset OppositeVertex, (∀ u v, oppositeK23.Adj u v → (u ∈ T ↔ v ∉ T)) → 4 ≤ T.card)
#synth DecidableRel oppositeK23.Adj
#synth DecidableEq OppositeVertex
#synth Fintype (Finset OppositeVertex)
set_option trace.Meta.synthInstance true in
#synth Decidable (∀ T : Finset OppositeVertex, (∀ u v, oppositeK23.Adj u v → (u ∈ T ↔ v ∉ T)) → 4 ≤ T.card)
end Erdos713Assembly
