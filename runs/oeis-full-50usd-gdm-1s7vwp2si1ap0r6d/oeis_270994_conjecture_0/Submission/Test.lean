import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

lemma a_odd (n : ℕ) : (a n) % 2 = 1 := by
  unfold a
  omega

lemma a_gt_1 (n : ℕ) : a n > 1 := by
  unfold a
  omega

lemma a_add_28_odd (n : ℕ) : (a n + 28) % 2 = 1 := by
  unfold a
  omega

lemma a_add_28_gt_1 (n : ℕ) : a n + 28 > 1 := by
  unfold a
  omega


def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)

#check ∀ n : ℕ, is_sierpinski_number (a n)

theorem test_unfold (n : ℕ) : is_sierpinski_number (a n) ↔ (a n % 2 = 1 ∧ a n > 1 ∧ ∀ m : ℕ, m > 0 → ¬ Nat.Prime (a n * 2^m + 1)) := by
  rfl

theorem test_n_0 :
  is_sierpinski_number (a 0) ∧
  is_sierpinski_number (a 0 + 28) ∧
  (∀ k : ℕ, is_sierpinski_number k → a 0 < k → k < a 0 + 28 → False) := by
  sorry

theorem test_prime_d10 : Nat.Prime (9454149 * 2^1 + 1) := by
  norm_num

theorem test_unfold_shadow (n : ℕ) : is_sierpinski_number (a n) ↔ (a n % 2 = 1 ∧ a n > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (a n * 2^n + 1)) := by
  rfl







