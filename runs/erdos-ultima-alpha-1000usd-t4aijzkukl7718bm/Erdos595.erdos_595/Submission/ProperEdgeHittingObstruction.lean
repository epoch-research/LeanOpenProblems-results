import Submission.SparseTransversalObstruction

/-!
A proper coloring of a subgraph meeting every triangle is a sufficient
covering certificate, but not a necessary one. In particular the global
smallest-pair ordering shortcut is too strong, even when the order is free.
This does not refute the separately local earlier-neighborhood criterion.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595ProperEdgeHitting
open Erdos595Work Erdos595SparseTransversalObstruction
variable {V C : Type*}

/-- At least one of the three edges of every G-triangle belongs to H. -/
def Hits (G H : SimpleGraph V) : Prop :=
  ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
    H.Adj a b ∨ H.Adj a c ∨ H.Adj b c

/-- A continuum-sized proper palette on an edge-hitting graph suffices.
H need not itself be a subgraph of G. -/
theorem cover_of_proper_hitting (G H : SimpleGraph V) (hh : Hits G H)
    (c : H.Coloring (ℕ → Fin 2)) : IsCountableUnionOfTriangleFree G := by
  apply countable_union_of_triangle_free_fibers G c
  intro a b d hab had hbd he
  rcases hh a b d hab had hbd with h | h | h
  · exact c.valid h he.1
  · exact c.valid h he.2
  · exact c.valid h (he.1.symm.trans he.2)

/-- Vertex Ramsey graphs obstruct every such hitting graph simultaneously. -/
theorem no_proper_hitting (G H : SimpleGraph V) (hG : VertexTriangleRamsey G C)
    (hh : Hits G H) : ¬Nonempty (H.Coloring C) := by
  rintro ⟨c⟩
  obtain ⟨a,b,d,hab,had,hbd,he₁,he₂⟩ := hG c
  rcases hh a b d hab had hbd with h | h | h
  · exact c.valid h he₁
  · exact c.valid h he₂
  · exact c.valid h (he₁.symm.trans he₂)

/-- Failure of all properly small edge-hitting certificates is compatible
with the existing two-piece shift-square edge cover. -/
theorem covered_no_proper_hitting (C : Type) [Nonempty C] :
    ∃ (V : Type) (G : SimpleGraph V), G.CliqueFree 4 ∧
      IsCountableUnionOfTriangleFree G ∧
      ∀ H : SimpleGraph V, Hits G H → ¬Nonempty (H.Coloring C) := by
  obtain ⟨A,oA,hA,hcov,hRam⟩ := shift_vertex_ramsey C
  letI : LinearOrder A := oA
  exact ⟨_,Erdos595MiddleCorner.graph A,hA,hcov,fun H hh => no_proper_hitting _ H hRam hh⟩

#print axioms cover_of_proper_hitting
#print axioms covered_no_proper_hitting
end Erdos595ProperEdgeHitting
