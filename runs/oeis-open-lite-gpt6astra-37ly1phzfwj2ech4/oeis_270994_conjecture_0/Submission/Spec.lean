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

theorem oeis_270994_conjecture_0.disproof : ¬ (type_of% @oeis_270994_conjecture_0) := by
  -- A finite covering certifies that this interior number is Sierpiński.
  have hcover (r : ℕ) (hr : r < 48) :
      ∃ p : ℕ, 2 ≤ p ∧ p ≤ 673 ∧ 2^48 % p = 1 ∧
        (5292270077783 * 2^r + 1) % p = 0 := by
    interval_cases r
    · exact ⟨3, by norm_num⟩
    · exact ⟨7, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨257, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨17, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨7, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨17, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨257, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨7, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨97, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨17, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨7, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨17, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨673, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨5, by norm_num⟩
  have hs : is_sierpinski_number 5292270077783 := by
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro n hn
    obtain ⟨p, hp₂, hpbound, hpperiod, hpcover⟩ :=
      hcover (n % 48) (Nat.mod_lt n (by norm_num))
    have hpow : 2^n % p = 2^(n%48) % p := by
      calc
        2^n % p = (2^(n%48) * (2^48)^(n/48)) % p := by
          rw [← pow_mul, ← pow_add, Nat.mod_add_div]
        _ = 2^(n%48) % p := by
          rw [Nat.mul_mod, Nat.pow_mod (2^48), hpperiod, one_pow,
            ← Nat.mul_mod, mul_one]
    have hmod : (5292270077783 * 2^n + 1) % p = 0 := by
      calc
        (5292270077783 * 2^n + 1) % p =
            (5292270077783 * 2^(n%48) + 1) % p := by
          simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, hpow]
        _ = 0 := hpcover
    apply Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hmod) hp₂
    have hpos := Nat.one_le_pow n 2 (by norm_num)
    nlinarith
  intro h
  exact (h 473165).2.2 5292270077783 hs (by norm_num [a]) (by norm_num [a])

