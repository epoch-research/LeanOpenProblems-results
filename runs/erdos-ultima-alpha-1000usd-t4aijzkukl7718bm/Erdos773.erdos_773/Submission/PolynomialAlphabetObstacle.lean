import FormalConjecturesUtil

/-!
Failure of an unrestricted coefficient-alphabet tensor construction.
These lemmas do not disprove Erdős 773.
-/

namespace Erdos773

lemma first_five_squares_sidon :
    IsSidon ((Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 5)) : Set ℕ) := by
  decide

lemma positive_alphabet_tensor_identity (x : ℕ) :
    (1 + x + x ^ 2 + 2 * x ^ 3) ^ 2 +
      (1 + 4 * x + 5 * x ^ 2 + 4 * x ^ 3) ^ 2 =
    (1 + 2 * x + 3 * x ^ 2 + 4 * x ^ 3) ^ 2 +
      (1 + 3 * x + 5 * x ^ 2 + 2 * x ^ 3) ^ 2 := by
  ring

lemma positive_alphabet_tensor_not_sidon (x : ℕ) (hx : 0 < x) :
    ¬ IsSidon ({(1 + x + x ^ 2 + 2 * x ^ 3) ^ 2,
      (1 + 4 * x + 5 * x ^ 2 + 4 * x ^ 3) ^ 2,
      (1 + 2 * x + 3 * x ^ 2 + 4 * x ^ 3) ^ 2,
      (1 + 3 * x + 5 * x ^ 2 + 2 * x ^ 3) ^ 2} : Set ℕ) := by
  intro hs
  have hpr : 1 + x + x ^ 2 + 2 * x ^ 3 < 1 + 2 * x + 3 * x ^ 2 + 4 * x ^ 3 := by
    omega
  have hps : 1 + x + x ^ 2 + 2 * x ^ 3 < 1 + 3 * x + 5 * x ^ 2 + 2 * x ^ 3 := by
    omega
  have hp2 := Nat.pow_lt_pow_left hpr (by omega : (2 : ℕ) ≠ 0)
  have hs2 := Nat.pow_lt_pow_left hps (by omega : (2 : ℕ) ≠ 0)
  have hh := hs _ (by simp) _ (by simp) _ (by simp) _ (by simp)
    (positive_alphabet_tensor_identity x)
  rcases hh with hh | hh <;> omega

lemma digit_permutation_norm_identity (a b c d x : ℤ) :
    (a + b * x + c * x ^ 2 + d * x ^ 3) ^ 2 +
      (d + c * x + b * x ^ 2 + a * x ^ 3) ^ 2 -
      (c + d * x + a * x ^ 2 + b * x ^ 3) ^ 2 -
      (b + a * x + d * x ^ 2 + c * x ^ 3) ^ 2 =
    (x - 1) ^ 2 * (x + 1) ^ 2 * (x ^ 2 + 1) * (a ^ 2 - b ^ 2 - c ^ 2 + d ^ 2) := by
  ring

#print axioms first_five_squares_sidon
#print axioms positive_alphabet_tensor_not_sidon
#print axioms digit_permutation_norm_identity

end Erdos773
