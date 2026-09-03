import FormalConjecturesUtil

/-!
An obstruction to a carry-free-root-addition digit-sphere construction.
This is not a disproof of Erdős 773.

The four words are monic binary-coefficient polynomials of the same degree,
evaluated in base 3. They have the same digit sum and squared-digit sum.
Adding any two root words causes no carries, but their integer squares still
have a nontrivial equal-sum collision. Carries in squaring remain relevant.
-/

namespace Erdos773

set_option maxHeartbeats 1000000

def carryFreeSphereWords : Fin 4 → Fin 10 → ℕ :=
  ![![1, 1, 1, 1, 1, 0, 0, 0, 0, 1],
    ![0, 1, 0, 0, 1, 1, 0, 1, 1, 1],
    ![0, 0, 1, 1, 1, 0, 1, 1, 0, 1],
    ![1, 1, 0, 1, 0, 1, 0, 0, 1, 1]]

def carryFreeSphereValue (j : Fin 4) : ℕ :=
  ∑ i : Fin 10, carryFreeSphereWords j i * 3 ^ i.val

lemma carry_free_sphere_digit_conditions :
    ∀ j : Fin 4,
      carryFreeSphereWords j 9 = 1 ∧
      (∀ i : Fin 10, carryFreeSphereWords j i ≤ 1) ∧
      (∑ i : Fin 10, carryFreeSphereWords j i) = 6 ∧
      (∑ i : Fin 10, (carryFreeSphereWords j i) ^ 2) = 6 := by
  decide

lemma carry_free_sphere_root_addition :
    ∀ (j k : Fin 4) (i : Fin 10),
      carryFreeSphereWords j i + carryFreeSphereWords k i < 3 := by
  decide

lemma carry_free_sphere_values :
    carryFreeSphereValue 0 = 19804 ∧
    carryFreeSphereValue 1 = 28758 ∧
    carryFreeSphereValue 2 = 22716 ∧
    carryFreeSphereValue 3 = 26518 := by
  decide

lemma carry_free_sphere_collision :
    (carryFreeSphereValue 0) ^ 2 + (carryFreeSphereValue 1) ^ 2 =
      (carryFreeSphereValue 2) ^ 2 + (carryFreeSphereValue 3) ^ 2 ∧
    Nat.gcd (Nat.gcd (carryFreeSphereValue 0) (carryFreeSphereValue 1))
      (Nat.gcd (carryFreeSphereValue 2) (carryFreeSphereValue 3)) = 2 ∧
    ¬ IsSidon (((Finset.univ : Finset (Fin 4)).image
      (fun j => (carryFreeSphereValue j) ^ 2)) : Set ℕ) := by
  decide

#print axioms carry_free_sphere_digit_conditions
#print axioms carry_free_sphere_root_addition
#print axioms carry_free_sphere_collision

end Erdos773
