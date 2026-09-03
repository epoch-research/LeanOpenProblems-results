import Submission.OrderedQuadNoArcCases

/-!
A kernel-checked finite order-constraint certificate excluding arc(K4).
The generated proof uses only equality, transitivity, and irreflexivity.
It does not establish non-coverability of the resulting right adjoint.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedVariables false
open SimpleGraph Set
namespace Erdos595OrderedQuadRight
open Erdos595ArcAdjoint
variable {A : Type*} [LinearOrder A]

private theorem no_diagram (v : Fin 12 → Quad A)
    (c0 : TriOptions (v 0) (v 4) (v 6))
    (c1 : TriOptions (v 0) (v 5) (v 9))
    (c2 : TriOptions (v 1) (v 3) (v 7))
    (c3 : TriOptions (v 1) (v 8) (v 9))
    (c4 : TriOptions (v 2) (v 3) (v 10))
    (c5 : TriOptions (v 2) (v 6) (v 11))
    (c6 : TriOptions (v 4) (v 8) (v 10))
    (c7 : TriOptions (v 5) (v 7) (v 11))
    (c8 : Adj (v 0) (v 3))
    (c9 : Adj (v 1) (v 6))
    (c10 : Adj (v 2) (v 9))
    (c11 : Adj (v 4) (v 7))
    (c12 : Adj (v 5) (v 10))
    (c13 : Adj (v 8) (v 11))
    : False := by
  rcases c0 with c0 | c0 | c0 | c0 | c0 | c0
  · exact no_diagram_0 v c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13
  · exact no_diagram_1 v c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13
  · exact no_diagram_2 v c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13
  · exact no_diagram_3 v c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13
  · exact no_diagram_4 v c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13
  · exact no_diagram_5 v c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13

private def arc (i : Fin 12) : Arc (⊤ : SimpleGraph (Fin 4)) :=
  ⟨(![(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2)] : Fin 12 → Fin 4 × Fin 4) i,by fin_cases i <;> decide⟩

private instance : DecidableRel (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj :=
  fun p q => inferInstanceAs (Decidable (p.val.2 = q.val.1 ∨ q.val.2 = p.val.1))

theorem no_arc_four : ¬Nonempty (arcGraph (⊤ : SimpleGraph (Fin 4)) →g graph A) := by
  rintro ⟨f⟩
  apply no_diagram (fun i => f (arc i))
  · apply triangle_options
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 0) (arc 4))
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 0) (arc 6))
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 4) (arc 6))
  · apply triangle_options
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 0) (arc 5))
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 0) (arc 9))
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 5) (arc 9))
  · apply triangle_options
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 1) (arc 3))
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 1) (arc 7))
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 3) (arc 7))
  · apply triangle_options
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 1) (arc 8))
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 1) (arc 9))
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 8) (arc 9))
  · apply triangle_options
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 2) (arc 3))
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 2) (arc 10))
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 3) (arc 10))
  · apply triangle_options
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 2) (arc 6))
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 2) (arc 11))
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 6) (arc 11))
  · apply triangle_options
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 4) (arc 8))
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 4) (arc 10))
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 8) (arc 10))
  · apply triangle_options
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 5) (arc 7))
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 5) (arc 11))
    · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 7) (arc 11))
  · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 0) (arc 3))
  · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 1) (arc 6))
  · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 2) (arc 9))
  · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 4) (arc 7))
  · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 5) (arc 10))
  · exact f.map_adj (by decide : (arcGraph (⊤ : SimpleGraph (Fin 4))).Adj (arc 8) (arc 11))

theorem right_cliqueFree : (right (graph A)).CliqueFree 4 := by
  by_contra h
  exact no_arc_four ((right_not_cliqueFree_iff (graph A) 4).mp h)

#print axioms no_arc_four
#print axioms right_cliqueFree
end Erdos595OrderedQuadRight
