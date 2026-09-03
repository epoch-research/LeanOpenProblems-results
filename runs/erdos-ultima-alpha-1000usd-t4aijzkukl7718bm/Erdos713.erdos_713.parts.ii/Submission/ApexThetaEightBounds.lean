import FormalConjecturesUtil
import Submission.ApexThetaFourteenNinths
import Submission.EightContainmentRefinement

/-! Explicit transfers of the 14/9 upper bound to representatives 17 and 23. -/
open Filter SimpleGraph Asymptotics
namespace Erdos713ApexThetaEightBounds
open Erdos713EightCore Erdos713EightRefinement Erdos713ApexThetaNinth
set_option maxHeartbeats 2000000

noncomputable def twenty_three_iso : Graph (representative 23) ≃g Erdos713GlobalTheta.pattern := by
  have hr : (fun i j => bit (representative 23) i j = true) = Erdos713GlobalTheta.bitRel := by
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  change Erdos713C6.bipGraph _ ≃g _
  rw [hr]
  exact Erdos713GlobalTheta.bitIso

lemma seventeen_contained : Graph (representative 17) ⊑ Erdos713GlobalTheta.pattern :=
  seventeen_contained_twenty_three.trans ⟨twenty_three_iso.toCopy⟩

lemma upper_seventeen :
    (fun n : ℕ => (extremalNumber n (Graph (representative 17)) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^((14 : ℝ)/9)) := upper_of_containment seventeen_contained

lemma upper_twenty_three :
    (fun n : ℕ => (extremalNumber n (Graph (representative 23)) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^((14 : ℝ)/9)) := upper_of_containment ⟨twenty_three_iso.toCopy⟩

lemma rate_bounds {i : Fin 32} (hi : i = 17 ∨ i = 23) {a : ℝ}
    (h : Erdos713Rate.HasRate (Graph (representative i)) a) :
    (3 : ℝ)/2 ≤ a ∧ a ≤ (14 : ℝ)/9 := by
  have hlo : Erdos713C4.K22 ⊑ Graph (representative i) := by
    rcases hi with rfl | rfl
    · exact (middle_containments 17 (by decide) (by decide) (by decide)).1
    · exact (middle_containments 23 (by decide) (by decide) (by decide)).1
  refine ⟨?_,?_⟩
  · apply Erdos713C4.lower_exponent_of_prime_bound h.upper
    intro p hp
    exact (Erdos713C4.extremal_lower_prime p hp).trans hlo.extremalNumber_le
  · rcases hi with rfl | rfl
    · exact h.lower _ (by norm_num) upper_seventeen
    · exact h.lower _ (by norm_num) upper_twenty_three

#print axioms twenty_three_iso
#print axioms upper_seventeen
#print axioms upper_twenty_three
#print axioms rate_bounds
end Erdos713ApexThetaEightBounds
