import FormalConjecturesUtil
import Submission.ThetaZeroDiamondMatching
import Submission.ThetaZeroTriangleMultiplicity

/-! The extra zero-diamond hypothesis does not follow from theta exclusion
and rigidity. This auxiliary obstruction does not disprove Erdős 713. -/
open Finset
open scoped Classical
namespace Erdos713ThetaZeroDiamondObstruction
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaDisjointSupports Erdos713ThetaRigidChargeExample
open Erdos713ThetaZeroTriangleMultiplicity Erdos713ThetaZeroDiamondMatching

lemma petal_hub_zero (N r : ℕ) (a : Rows N) (j : Fin r) {s : Fin 3}
    (hs : a.1 ≠ s) : codegree (Inc N r) (petal a j) (hub s) = 0 := by
  letI : IsEmpty {b : Rows N // Inc N r b (petal a j) ∧ Inc N r b (hub s)} :=
    ⟨fun b => hs ((congrArg Prod.fst b.property.1).symm.trans b.property.2)⟩
  exact Nat.card_of_isEmpty

theorem not_noZeroDiamond (N r : ℕ) (i : Fin N) (j : Fin r) :
    ¬ NoZeroDiamond (Inc N r) := by
  intro hz
  have hpos : codegree (Inc N r) (hub 0) (petal (0,i) j) ≠ 0 := by
    intro he
    exact not_common_of_codegree_zero he (0,i) ⟨rfl,rfl⟩
  exact hz (hub 0) (petal (0,i) j) (hub 1) (hub 2)
    (by simp [hub,petal]) (by simp [hub]) (by simp [hub])
    (by simp [hub,petal]) (by simp [hub,petal]) (by simp [hub])
    hpos (hubs_codegree_zero N r (by decide : (0 : Fin 3) ≠ 1))
    (hubs_codegree_zero N r (by decide : (0 : Fin 3) ≠ 2))
    (petal_hub_zero N r (0,i) j (by decide : (0 : Fin 3) ≠ 1))
    (petal_hub_zero N r (0,i) j (by decide : (0 : Fin 3) ≠ 2))
    (hubs_codegree_zero N r (by decide : (1 : Fin 3) ≠ 2))

/-- Arbitrarily large uniform row degree does not supply the missing
zero-diamond exclusion. -/
theorem rigid_large_example (N r : ℕ) (i : Fin N) :
    ¬ HasTheta (Inc N (r+1)) ∧
    (∀ a b, a ≠ b → (row (Inc N (r+1)) a ∩ row (Inc N (r+1)) b).card ≤ 2) ∧
    (∀ a, (row (Inc N (r+1)) a).card = r+4) ∧
    ¬ NoZeroDiamond (Inc N (r+1)) := by
  refine ⟨no_theta N (r+1),rigid N (r+1),?_,not_noZeroDiamond N (r+1) i 0⟩
  intro a
  simpa only [Nat.add_assoc] using row_card N (r+1) a

#print axioms not_noZeroDiamond
#print axioms rigid_large_example
end Erdos713ThetaZeroDiamondObstruction
