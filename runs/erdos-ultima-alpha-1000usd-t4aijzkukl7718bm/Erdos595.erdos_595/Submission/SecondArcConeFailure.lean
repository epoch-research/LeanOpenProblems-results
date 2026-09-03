import Submission.SecondArcTransversal
import Submission.SecondConeCliqueCover
import Submission.ThirdArcBacktrackingFailure

/-!
The independent-transversal cone factorization can create a four-clique in
its second right adjoint, even when the original graph is the diamond.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595SecondArcConeFailure
open Erdos595ArcAdjoint Erdos595Work Erdos595SecondArcTransversal
abbrev D := Erdos595ThirdArcFailure.diamond

local instance : DecidableRel (arcGraph D).Adj := fun p q =>
  inferInstanceAs (Decidable (p.val.2 = q.val.1 ∨ q.val.2 = p.val.1))
local instance : DecidableRel (arcGraph (arcGraph D)).Adj := fun p q =>
  inferInstanceAs (Decidable (p.val.2 = q.val.1 ∨ q.val.2 = p.val.1))

def points : Fin 5 → Arc (arcGraph D) := ![
  ⟨(⟨(0,1),by decide⟩,⟨(1,2),by decide⟩),by decide⟩,
  ⟨(⟨(1,2),by decide⟩,⟨(0,1),by decide⟩),by decide⟩,
  ⟨(⟨(0,1),by decide⟩,⟨(2,0),by decide⟩),by decide⟩,
  ⟨(⟨(2,0),by decide⟩,⟨(3,2),by decide⟩),by decide⟩,
  ⟨(⟨(1,2),by decide⟩,⟨(2,0),by decide⟩),by decide⟩]

lemma not_selected : ∀ i : Fin 5, ¬Selected D (points i) := by
  unfold Selected points
  decide +kernel

lemma adjacent : ∀ i : Fin 5,
    (arcGraph (arcGraph D)).Adj (points i) (points (i + 1)) := by decide +kernel

def basePoint (i : Fin 5) : {p // ¬Selected D p} := ⟨points i,not_selected i⟩

lemma base_adj (i : Fin 5) : (Base D).Adj (basePoint i) (basePoint (i+1)) := adjacent i

/-- This particular cone base has a closed five-step walk. -/
theorem not_noFive : ¬Erdos595SecondConeRight.NoFive (Base D) := by
  intro h
  exact h (basePoint 0) (basePoint 1) (basePoint 2) (basePoint 3) (basePoint 4)
    (base_adj 0) (base_adj 1) (base_adj 2) (base_adj 3) (base_adj 4)

/-- Thus the factorization does NOT preserve the K4 bound at its target. -/
theorem creates_four : D.CliqueFree 4 ∧
    ¬(right (right (coneGraph (Base D)))).CliqueFree 4 :=
  ⟨Erdos595ThirdArcFailure.diamond_cliqueFree,
    fun h => not_noFive (Erdos595SecondConeClique.noFive_of_cliqueFree (Base D) h)⟩

#print axioms not_selected
#print axioms not_noFive
#print axioms creates_four
end Erdos595SecondArcConeFailure
