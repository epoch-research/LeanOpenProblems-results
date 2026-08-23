import FormalConjectures.Util.ProblemImports

/--
A270994: $a(n) = 9454129 + 11184810 \cdot n$.
-/
def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

/-- A natural number `k` is a Sierpiński number if it is odd, greater than 1,
    and for all positive natural numbers `n`, $k \cdot 2^n + 1$ is not a prime number. -/
def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)

/--
oeis_270994_conjecture_0: Are a(n) and a(n) + 28 always consecutive Sierpiński numbers?

This conjecture asserts that for all $n$, $a(n)$ and $a(n)+28$ are Sierpiński numbers,
and there are no Sierpiński numbers strictly between them.
-/
private lemma factor_not_prime {k e p : ℕ} (hp2 : 2 ≤ p) (hp : p < k)
    (hd : p ∣ k * 2^e + 1) : ¬ Nat.Prime (k * 2^e + 1) := by
  apply Nat.not_prime_of_dvd_of_lt hd hp2
  exact lt_of_lt_of_le hp (le_trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega)))
    (Nat.le_add_right _ _))

private lemma counterexample_is_sierpinski : is_sierpinski_number 59496778573193 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro e he
  have hc : e % 2 = 0 ∨ e % 4 = 3 ∨ e % 3 = 1 ∨ e % 8 = 1 ∨
      e % 48 = 5 ∨ e % 48 = 21 ∨ e % 16 = 13 := by
    have hr := Nat.mod_lt e (by omega : 0 < 48)
    interval_cases h : e % 48 <;> omega
  rcases hc with h | h | h | h | h | h | h
  · obtain ⟨q, rfl⟩ : ∃ q, e = 2*q := by use e/2; omega
    apply factor_not_prime (p := 3) (by norm_num) (by norm_num)
    rw [Nat.dvd_iff_mod_eq_zero]
    simp [pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  · obtain ⟨q, rfl⟩ : ∃ q, e = 4*q+3 := by use e/4; omega
    apply factor_not_prime (p := 5) (by norm_num) (by norm_num)
    rw [Nat.dvd_iff_mod_eq_zero]
    simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  · obtain ⟨q, rfl⟩ : ∃ q, e = 3*q+1 := by use e/3; omega
    apply factor_not_prime (p := 7) (by norm_num) (by norm_num)
    rw [Nat.dvd_iff_mod_eq_zero]
    simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  · obtain ⟨q, rfl⟩ : ∃ q, e = 8*q+1 := by use e/8; omega
    apply factor_not_prime (p := 17) (by norm_num) (by norm_num)
    rw [Nat.dvd_iff_mod_eq_zero]
    simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  · obtain ⟨q, rfl⟩ : ∃ q, e = 48*q+5 := by use e/48; omega
    apply factor_not_prime (p := 97) (by norm_num) (by norm_num)
    rw [Nat.dvd_iff_mod_eq_zero]
    simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  · obtain ⟨q, rfl⟩ : ∃ q, e = 48*q+21 := by use e/48; omega
    apply factor_not_prime (p := 673) (by norm_num) (by norm_num)
    rw [Nat.dvd_iff_mod_eq_zero]
    simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  · obtain ⟨q, rfl⟩ : ∃ q, e = 16*q+13 := by use e/16; omega
    apply factor_not_prime (p := 257) (by norm_num) (by norm_num)
    rw [Nat.dvd_iff_mod_eq_zero]
    simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

theorem oeis_270994_conjecture_0.disproof : ¬ (∀ n : ℕ,
    is_sierpinski_number (a n) ∧
    is_sierpinski_number (a n + 28) ∧
    (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False)) := by
  intro h
  have hn := h 5319426
  exact hn.2.2 59496778573193 counterexample_is_sierpinski
    (by norm_num [a]) (by norm_num [a])
