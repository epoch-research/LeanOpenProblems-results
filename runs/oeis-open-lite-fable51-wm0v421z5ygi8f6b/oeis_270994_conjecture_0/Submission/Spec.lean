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
theorem oeis_270994_conjecture_0 : ∀ n : ℕ,
  is_sierpinski_number (a n) ∧
  is_sierpinski_number (a n + 28) ∧
  (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False) := by
  sorry

/-- Periodicity of powers of two modulo `p`. -/
lemma two_pow_modEq_period (p N m : ℕ) (h : 2 ^ N ≡ 1 [MOD p]) :
    2 ^ m ≡ 2 ^ (m % N) [MOD p] := by
  have h1 : 2 ^ m = (2 ^ N) ^ (m / N) * 2 ^ (m % N) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  calc 2 ^ m = (2 ^ N) ^ (m / N) * 2 ^ (m % N) := h1
    _ ≡ 1 ^ (m / N) * 2 ^ (m % N) [MOD p] := Nat.ModEq.mul_right _ (Nat.ModEq.pow _ h)
    _ = 2 ^ (m % N) := by simp

/-- `k = 5292270077783 = a 473165 + 4` is a Sierpiński number, with covering set
`{3, 5, 7, 17, 97, 257, 673}` (period 48). -/
lemma sierpinski_5292270077783 : is_sierpinski_number 5292270077783 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro m hm hprime
  have H : ∀ p : ℕ, 1 < p → p < 5292270077783 → 2 ^ 48 % p = 1 →
      (5292270077783 * 2 ^ (m % 48) + 1) % p = 0 → False := by
    intro p hp1 hpk hper hmod
    have hme : 2 ^ m ≡ 2 ^ (m % 48) [MOD p] :=
      two_pow_modEq_period p 48 m (by unfold Nat.ModEq; rw [hper]; exact (Nat.mod_eq_of_lt hp1).symm)
    have hme2 : 5292270077783 * 2 ^ m + 1 ≡ 5292270077783 * 2 ^ (m % 48) + 1 [MOD p] :=
      (hme.mul_left _).add_right 1
    have hdvd : p ∣ 5292270077783 * 2 ^ m + 1 :=
      (hme2.dvd_iff dvd_rfl).mpr (Nat.dvd_of_mod_eq_zero hmod)
    rcases hprime.eq_one_or_self_of_dvd p hdvd with h1 | h1
    · omega
    · have : 5292270077783 ≤ 5292270077783 * 2 ^ m :=
        Nat.le_mul_of_pos_right _ (by positivity)
      omega
  have hr : m % 48 < 48 := Nat.mod_lt _ (by norm_num)
  obtain ⟨r, hr'⟩ : ∃ r, r = m % 48 := ⟨_, rfl⟩
  rw [← hr'] at H hr
  interval_cases r
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 257 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 257 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 97 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 673 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact H 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem oeis_270994_conjecture_0.disproof : ¬ (type_of% @oeis_270994_conjecture_0) := by
  intro h
  obtain ⟨-, -, h3⟩ := h 473165
  exact h3 5292270077783 sierpinski_5292270077783 (by norm_num [a]) (by norm_num [a])
