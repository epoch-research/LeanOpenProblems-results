import FormalConjecturesUtil

/-!
An obstruction to a proposed lower-bound construction, not a disproof of Erdős 773.
The four words are monic degree-six base-81 digit polynomials. Every lower
coefficient is divisible by 3, the constant coefficient is 3 modulo 9,
and all four coefficient sums are 229. Their evaluations nevertheless have
a nontrivial square-sum collision, with no common factor beyond the forced 3.
-/

namespace Erdos773

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def eisensteinMomentWords : Fin 4 → Fin 7 → ℕ :=
  ![![21, 54, 66, 63, 24, 0, 1],
    ![75, 3, 0, 21, 75, 54, 1],
    ![30, 24, 63, 3, 54, 54, 1],
    ![39, 45, 75, 9, 60, 0, 1]]

def eisensteinMomentValue (j : Fin 4) : ℕ :=
  ∑ i : Fin 7, eisensteinMomentWords j i * 81 ^ i.val

lemma eisenstein_fixed_digit_sum_pattern :
    ∀ j : Fin 4,
      eisensteinMomentWords j 6 = 1 ∧
      eisensteinMomentWords j 0 % 9 = 3 ∧
      (∀ i : Fin 7, eisensteinMomentWords j i < 81 ∧
        (i.val < 6 → 3 ∣ eisensteinMomentWords j i)) ∧
      (∑ i : Fin 7, eisensteinMomentWords j i) = 229 := by
  decide

lemma eisenstein_fixed_digit_sum_values :
    eisensteinMomentValue 0 = 283496575989 ∧
    eisensteinMomentValue 1 = 473955558789 ∧
    eisensteinMomentValue 2 = 473042426709 ∧
    eisensteinMomentValue 3 = 285017618469 := by
  decide

lemma eisenstein_fixed_digit_sum_collision :
    (eisensteinMomentValue 0) ^ 2 + (eisensteinMomentValue 1) ^ 2 =
      (eisensteinMomentValue 2) ^ 2 + (eisensteinMomentValue 3) ^ 2 ∧
    Nat.gcd (Nat.gcd (eisensteinMomentValue 0) (eisensteinMomentValue 1))
      (Nat.gcd (eisensteinMomentValue 2) (eisensteinMomentValue 3)) = 3 ∧
    ¬ IsSidon (((Finset.univ : Finset (Fin 4)).image
      (fun j => (eisensteinMomentValue j) ^ 2)) : Set ℕ) := by
  decide

#print axioms eisenstein_fixed_digit_sum_pattern
#print axioms eisenstein_fixed_digit_sum_collision

end Erdos773
