import Submission.ThinMarkedSecondRight

/-!
Adjoin any family of independent vertices, each having at most two old
neighbors, to a triangle-free graph. The full second right adjoint always
has a TWO-piece triangle-free edge cover. In particular, attaching private
triangles to base edges does not amplify countable edge-color obstructions.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595EdgeEarSecondRight
open Erdos595ArcAdjoint Erdos595ThinMarkedSecondRight
variable {V E : Type*} (B : SimpleGraph V) (l r : E → V)

/-- An arbitrary indexed family of two-neighbor ears. The endpoints need
not be adjacent; repetitions and multiple ears at the same pair are allowed. -/
def graph : SimpleGraph (V ⊕ E) where
  Adj
    | .inl a, .inl b => B.Adj a b
    | .inl a, .inr e => a = l e ∨ a = r e
    | .inr e, .inl a => l e = a ∨ r e = a
    | .inr _, .inr _ => False
  symm := by
    intro a b
    cases a <;> cases b
    · exact SimpleGraph.Adj.symm
    · exact Or.imp Eq.symm Eq.symm
    · exact Or.imp Eq.symm Eq.symm
    · exact id
  loopless := by
    intro a
    cases a
    · exact B.loopless _
    · exact id

def mark : V ⊕ E → Bool
  | .inl _ => false
  | .inr _ => true

variable (hB : B.CliqueFree 3)

include hB in
theorem mark_exact :
    Erdos595ExactTransversalRight.ExactTransversal (graph B l r) mark := by
  classical
  intro a b c hab hac hbc
  cases a <;> cases b <;> cases c <;>
    simp_all only [graph,mark,Bool.toNat_false,Bool.toNat_true,Nat.zero_add,Nat.add_zero]
  exact (hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)).elim

theorem mark_thin : Thin (graph B l r) mark := by
  intro a b c ha hab hac hbc d had
  cases a with
  | inl a => cases ha
  | inr e =>
    cases b with
    | inr b => exact hab.elim
    | inl b =>
      cases c with
      | inr c => exact hac.elim
      | inl c =>
        cases d with
        | inr d => exact had.elim
        | inl d =>
          change l e = b ∨ r e = b at hab
          change l e = c ∨ r e = c at hac
          change l e = d ∨ r e = d at had
          change B.Adj b c at hbc
          have hne := hbc.ne
          simp only [Sum.inl.injEq]
          rcases hab with hb | hb <;> rcases hac with hc | hc <;>
            rcases had with hd | hd <;> simp_all

include hB in
/-- No cardinality or proper vertex-coloring bound on B is assumed. -/
theorem second_right_two_cover :
    Erdos595CompleteFilterEdgeCover.CoversWith
      (right (right (graph B l r))) 2 :=
  Erdos595ThinMarkedSecondRight.second_right_two_cover (graph B l r) mark
    (mark_exact B l r hB) (mark_thin B l r)

include hB in
theorem second_right_cover :
    Erdos595Work.IsCountableUnionOfTriangleFree (right (right (graph B l r))) :=
  (show Erdos595BadEdge.FiniteCover (right (right (graph B l r))) from
    ⟨2,second_right_two_cover B l r hB⟩).countable

#print axioms mark_thin
#print axioms second_right_two_cover
#print axioms second_right_cover
end Erdos595EdgeEarSecondRight
