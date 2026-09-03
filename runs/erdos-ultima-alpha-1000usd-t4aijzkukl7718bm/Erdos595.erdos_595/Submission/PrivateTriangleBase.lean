import Submission.ArcAdjoint

/-! The graph operation adjoining private triangles at bare vertices. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595PrivateTriangleCompletion
open Erdos595ArcAdjoint
variable {V : Type*} (H : SimpleGraph V)

/-- The old neighborhood is independent. -/
def Bare (v : V) : Prop := ∀ a b, H.Adj v a → H.Adj v b → ¬H.Adj a b
abbrev Center := {v : V // Bare H v}
abbrev Vertex := V ⊕ (Center H × Bool)

def graph : SimpleGraph (Vertex H) where
  Adj
    | .inl a, .inl b => H.Adj a b
    | .inl a, .inr b => a = b.1.val
    | .inr a, .inl b => a.1.val = b
    | .inr a, .inr b => a.1 = b.1 ∧ a.2 ≠ b.2
  symm := by
    intro a b
    cases a <;> cases b
    · exact fun h => h.symm
    · exact Eq.symm
    · exact Eq.symm
    · exact fun h => ⟨h.1.symm,h.2.symm⟩
  loopless := by
    intro a
    cases a
    · exact H.loopless _
    · exact fun h => h.2 rfl

def oldEmbedding : H ↪g graph H where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl

end Erdos595PrivateTriangleCompletion
