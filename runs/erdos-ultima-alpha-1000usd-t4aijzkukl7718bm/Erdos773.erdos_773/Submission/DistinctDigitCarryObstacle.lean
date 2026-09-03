import FormalConjecturesUtil

/-!
A counterexample to a proposed specialization rule, not to Erdős 773.
Distinct digit permutations, inert-prime Eisenstein conditions, prime base,
and pairwise coprime roots can coexist with a nontrivial square-sum collision.
-/
namespace Erdos773.DistinctDigitCarry
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def words (u v : ℕ) : Fin 4 → Fin 28 → ℕ :=
  ![![3,33,42,72,102,63,v+21,9,69,66,216,366,219,3*v+63,
      15,195,270,360,450,285,5*v+105,3*u,30*u,12*u,60*u,42*u,21*u,1],
    ![3,63,102,72,42,33,v+21,15,285,450,360,270,195,5*v+105,
      9,219,366,216,66,69,3*v+63,3*u,60*u,42*u,30*u,12*u,21*u,1],
    ![3,63,102,72,42,33,v+21,9,219,366,216,66,69,3*v+63,
      15,285,450,360,270,195,5*v+105,3*u,60*u,42*u,30*u,12*u,21*u,1],
    ![3,33,42,72,102,63,v+21,15,195,270,360,450,285,5*v+105,
      9,69,66,216,366,219,3*v+63,3*u,30*u,12*u,60*u,42*u,21*u,1]]

def value (u v B : ℕ) (j : Fin 4) : ℕ :=
  ∑ i : Fin 28, words u v j i * B ^ i.val

lemma histogram_perm (u v : ℕ) (j : Fin 4) :
    List.Perm (List.ofFn (words u v j)) (List.ofFn (words u v 0)) := by
  apply List.perm_iff_count.mpr
  intro a
  fin_cases j <;> simp [words, List.ofFn_succ, List.count_cons] <;> omega

lemma digit_sum (u v : ℕ) (j : Fin 4) :
    (∑ i : Fin 28, words u v j i) = 168 * u + 9 * v + 3025 := by
  fin_cases j <;> simp [words, Fin.sum_univ_succ] <;> ring

lemma digit_norm (u v : ℕ) (j : Fin 4) :
    (∑ i : Fin 28, words u v j i ^ 2) =
      6858 * u ^ 2 + 35 * v ^ 2 + 1470 * v + 800101 := by
  fin_cases j <;> simp [words, Fin.sum_univ_succ] <;> ring

lemma value_expand_0 (u v B : ℕ) : value u v B 0 =
    (3) * B ^ 0 +
    (33) * B ^ 1 +
    (42) * B ^ 2 +
    (72) * B ^ 3 +
    (102) * B ^ 4 +
    (63) * B ^ 5 +
    (v + 21) * B ^ 6 +
    (9) * B ^ 7 +
    (69) * B ^ 8 +
    (66) * B ^ 9 +
    (216) * B ^ 10 +
    (366) * B ^ 11 +
    (219) * B ^ 12 +
    (3*v + 63) * B ^ 13 +
    (15) * B ^ 14 +
    (195) * B ^ 15 +
    (270) * B ^ 16 +
    (360) * B ^ 17 +
    (450) * B ^ 18 +
    (285) * B ^ 19 +
    (5*v + 105) * B ^ 20 +
    (3*u) * B ^ 21 +
    (30*u) * B ^ 22 +
    (12*u) * B ^ 23 +
    (60*u) * B ^ 24 +
    (42*u) * B ^ 25 +
    (21*u) * B ^ 26 +
    (1) * B ^ 27 := by
  simp [value, words, Fin.sum_univ_succ, add_assoc]

lemma value_expand_1 (u v B : ℕ) : value u v B 1 =
    (3) * B ^ 0 +
    (63) * B ^ 1 +
    (102) * B ^ 2 +
    (72) * B ^ 3 +
    (42) * B ^ 4 +
    (33) * B ^ 5 +
    (v + 21) * B ^ 6 +
    (15) * B ^ 7 +
    (285) * B ^ 8 +
    (450) * B ^ 9 +
    (360) * B ^ 10 +
    (270) * B ^ 11 +
    (195) * B ^ 12 +
    (5*v + 105) * B ^ 13 +
    (9) * B ^ 14 +
    (219) * B ^ 15 +
    (366) * B ^ 16 +
    (216) * B ^ 17 +
    (66) * B ^ 18 +
    (69) * B ^ 19 +
    (3*v + 63) * B ^ 20 +
    (3*u) * B ^ 21 +
    (60*u) * B ^ 22 +
    (42*u) * B ^ 23 +
    (30*u) * B ^ 24 +
    (12*u) * B ^ 25 +
    (21*u) * B ^ 26 +
    (1) * B ^ 27 := by
  simp [value, words, Fin.sum_univ_succ, add_assoc]

lemma value_expand_2 (u v B : ℕ) : value u v B 2 =
    (3) * B ^ 0 +
    (63) * B ^ 1 +
    (102) * B ^ 2 +
    (72) * B ^ 3 +
    (42) * B ^ 4 +
    (33) * B ^ 5 +
    (v + 21) * B ^ 6 +
    (9) * B ^ 7 +
    (219) * B ^ 8 +
    (366) * B ^ 9 +
    (216) * B ^ 10 +
    (66) * B ^ 11 +
    (69) * B ^ 12 +
    (3*v + 63) * B ^ 13 +
    (15) * B ^ 14 +
    (285) * B ^ 15 +
    (450) * B ^ 16 +
    (360) * B ^ 17 +
    (270) * B ^ 18 +
    (195) * B ^ 19 +
    (5*v + 105) * B ^ 20 +
    (3*u) * B ^ 21 +
    (60*u) * B ^ 22 +
    (42*u) * B ^ 23 +
    (30*u) * B ^ 24 +
    (12*u) * B ^ 25 +
    (21*u) * B ^ 26 +
    (1) * B ^ 27 := by
  simp [value, words, Fin.sum_univ_succ, add_assoc]

lemma value_expand_3 (u v B : ℕ) : value u v B 3 =
    (3) * B ^ 0 +
    (33) * B ^ 1 +
    (42) * B ^ 2 +
    (72) * B ^ 3 +
    (102) * B ^ 4 +
    (63) * B ^ 5 +
    (v + 21) * B ^ 6 +
    (15) * B ^ 7 +
    (195) * B ^ 8 +
    (270) * B ^ 9 +
    (360) * B ^ 10 +
    (450) * B ^ 11 +
    (285) * B ^ 12 +
    (5*v + 105) * B ^ 13 +
    (9) * B ^ 14 +
    (69) * B ^ 15 +
    (66) * B ^ 16 +
    (216) * B ^ 17 +
    (366) * B ^ 18 +
    (219) * B ^ 19 +
    (3*v + 63) * B ^ 20 +
    (3*u) * B ^ 21 +
    (30*u) * B ^ 22 +
    (12*u) * B ^ 23 +
    (60*u) * B ^ 24 +
    (42*u) * B ^ 25 +
    (21*u) * B ^ 26 +
    (1) * B ^ 27 := by
  simp [value, words, Fin.sum_univ_succ, add_assoc]

lemma norm_difference_factor (u v B : ℕ) :
    (value u v B 0 : ℤ) ^ 2 + (value u v B 1 : ℤ) ^ 2 -
      (value u v B 2 : ℤ) ^ 2 - (value u v B 3 : ℤ) ^ 2 =
      120 * (B : ℤ) ^ 35 * ((B : ℤ) - 1) ^ 2 * ((B : ℤ) + 1) ^ 2 *
        ((u : ℤ) * v - B - 1) *
        ((B : ℤ) ^ 6 + B ^ 5 + B ^ 4 + B ^ 3 + B ^ 2 + B + 1) := by
  rw [value_expand_0, value_expand_1, value_expand_2, value_expand_3]
  push_cast
  ring

lemma collision (u v B : ℕ) (hB : B + 1 = u * v) :
    value u v B 0 ^ 2 + value u v B 1 ^ 2 =
      value u v B 2 ^ 2 + value u v B 3 ^ 2 := by
  have h := norm_difference_factor u v B
  have hB' : (B : ℤ) + 1 = (u : ℤ) * v := by exact_mod_cast hB
  have hz : (u : ℤ) * v - B - 1 = 0 := by omega
  rw [hz] at h
  simp only [mul_zero, zero_mul] at h
  have hh : (value u v B 0 : ℤ) ^ 2 + (value u v B 1 : ℤ) ^ 2 =
      (value u v B 2 : ℤ) ^ 2 + (value u v B 3 : ℤ) ^ 2 := by omega
  exact_mod_cast hh

lemma concrete_prime_base : Nat.Prime 372689 := by norm_num

lemma concrete_digit_conditions : ∀ j : Fin 4,
    words 615 606 j 27 = 1 ∧ words 615 606 j 0 = 3 ∧
      Function.Injective (words 615 606 j) ∧
      (∀ i : Fin 28, 0 < words 615 606 j i ∧ 2 * words 615 606 j i < 372689 ∧
        (i.val < 27 → 3 ∣ words 615 606 j i)) ∧
      (∑ i : Fin 28, words 615 606 j i) < 372689 := by
  decide +kernel

lemma concrete_pairwise_coprime :
    Pairwise (fun i j : Fin 4 => (value 615 606 372689 i).Coprime
      (value 615 606 372689 j)) := by
  unfold Pairwise
  decide +kernel

lemma concrete_not_sidon :
    ¬ IsSidon (((Finset.univ : Finset (Fin 4)).image
      (fun j => value 615 606 372689 j ^ 2)) : Set ℕ) := by
  intro hs
  have h := hs (value 615 606 372689 0 ^ 2) (by simp)
    (value 615 606 372689 2 ^ 2) (by simp)
    (value 615 606 372689 1 ^ 2) (by simp)
    (value 615 606 372689 3 ^ 2) (by simp)
    (collision 615 606 372689 (by norm_num))
  have h02 : value 615 606 372689 0 ^ 2 ≠ value 615 606 372689 2 ^ 2 := by decide +kernel
  have h03 : value 615 606 372689 0 ^ 2 ≠ value 615 606 372689 3 ^ 2 := by decide +kernel
  rcases h with h | h
  · exact h02 h.1
  · exact h03 h.1

/-- All these proposed extra conditions hold, yet the evaluated squares are not Sidon. -/
theorem distinct_digit_conditions_do_not_suffice :
    ∃ B : ℕ, ∃ w : Fin 4 → Fin 28 → ℕ,
      B.Prime ∧
      (∀ j, w j 27 = 1 ∧ w j 0 = 3 ∧ Function.Injective (w j) ∧
        (∀ i, 0 < w j i ∧ 2 * w j i < B ∧ (i.val < 27 → 3 ∣ w j i)) ∧
        (∑ i, w j i) < B) ∧
      (∀ j, List.Perm (List.ofFn (w j)) (List.ofFn (w 0))) ∧
      Pairwise (fun i j : Fin 4 =>
        (∑ k : Fin 28, w i k * B ^ k.val).Coprime (∑ k : Fin 28, w j k * B ^ k.val)) ∧
      ¬ IsSidon (((Finset.univ : Finset (Fin 4)).image
        (fun j => (∑ k : Fin 28, w j k * B ^ k.val) ^ 2)) : Set ℕ) := by
  exact ⟨372689, words 615 606, concrete_prime_base, concrete_digit_conditions,
    histogram_perm 615 606, concrete_pairwise_coprime, concrete_not_sidon⟩

#print axioms norm_difference_factor
#print axioms concrete_digit_conditions
#print axioms concrete_pairwise_coprime
#print axioms distinct_digit_conditions_do_not_suffice
end Erdos773.DistinctDigitCarry
