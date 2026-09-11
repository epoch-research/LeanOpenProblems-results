import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A268597: Smallest $x$ such that $x-1 \pmod{\phi(x)} = n$, or $0$ if no such $x$ exists.
-/
noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

/-! ### Verified partial results

`A268597 n > 0` is equivalent to the existence of a witness `x > 0` with `(x - 1) % φ x = n`,
i.e. (with `N = n + 1`) to `N = x mod φ x` (or `N = φ x` when `φ x ∣ x`).  Writing
`N = 2^a * M` with `M` odd, the following families are proved unconditionally:
`M = 1` (`x = 2^(a+1)`), `M` prime (`x = 2^a * M^2`), `M = 3^b` (`x = 2^a * 3^(b+1)`),
and `M + 1 = p + q` for distinct primes `p, q ≥ 5` (`x = 2^a * p * q`).
The last family is a Goldbach-type condition; `conjecture_of_goldbach` below shows that it
implies the full conjecture.  Numerically, for `N = 91, 95, 217, …` the *only* witnesses are
`x = p * q` with `p + q = N + 1`, so the conjecture is at least as strong as a binary
Goldbach statement for infinitely many `n`; this is why the main theorem is left open.
-/

theorem A268597_pos_of_witness {n x : ℕ} (hx : 0 < x) (h : (x - 1) % Nat.totient x = n) :
    A268597 n > 0 := by
  have hne : ({x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n}).Nonempty := ⟨x, hx, h⟩
  exact (Nat.sInf_mem hne).1

/-- Key arithmetic step: if `x = r + 1 + k * m` and `r < m` then `(x - 1) % m = r`. -/
theorem pred_mod_eq {x m k r : ℕ} (h : x = r + 1 + k * m) (hr : r < m) : (x - 1) % m = r := by
  have h' : x - 1 = r + k * m := by omega
  rw [h', mul_comm, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hr

/-- `n + 1 = 2^a * p` with `p` an odd prime: witness `x = 2^a * p^2`. -/
theorem case_pow_two_mul_prime (n a p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn : n + 1 = 2 ^ a * p) :
    A268597 n > 0 := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hcop : Nat.Coprime (2 ^ a) (p ^ 2) := by
    apply Nat.Coprime.pow
    exact (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  apply A268597_pos_of_witness (x := 2 ^ a * p ^ 2) (by positivity)
  rw [Nat.totient_mul hcop, Nat.totient_prime_pow hp (by omega)]
  obtain ⟨A, rfl⟩ : ∃ A, p = A + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.reduceSub, pow_one]
  rcases a with _ | a
  · simp only [pow_zero, one_mul, Nat.totient_one] at hn ⊢
    apply pred_mod_eq (k := 1)
    · rw [hn]; ring
    · nlinarith
  · rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp only [Nat.add_sub_cancel, Nat.reduceSub, mul_one]
    apply pred_mod_eq (k := 2)
    · rw [hn]; ring
    · have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      have : 2 ^ (a + 1) * (A + 1) = 2 * (2 ^ a * (A + 1)) := by ring
      rw [this] at hn
      nlinarith

/-- `n + 1 = 2^a * 3^b` with `b ≥ 1`: witness `x = 2^a * 3^(b+1)`. -/
theorem case_pow_two_mul_pow_three (n a b : ℕ) (hb : 1 ≤ b) (hn : n + 1 = 2 ^ a * 3 ^ b) :
    A268597 n > 0 := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have hcop : Nat.Coprime (2 ^ a) (3 ^ (b + 1)) := by
    apply Nat.Coprime.pow
    exact (Nat.coprime_primes Nat.prime_two h3).2 (by norm_num)
  apply A268597_pos_of_witness (x := 2 ^ a * 3 ^ (b + 1)) (by positivity)
  rw [Nat.totient_mul hcop, Nat.totient_prime_pow h3 (by omega)]
  simp only [Nat.add_sub_cancel, Nat.reduceSub]
  have h3b : 1 ≤ 3 ^ b := Nat.one_le_pow _ _ (by norm_num)
  rcases a with _ | a
  · simp only [pow_zero, one_mul, Nat.totient_one] at hn ⊢
    apply pred_mod_eq (k := 1)
    · rw [hn]; ring
    · omega
  · rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp only [Nat.add_sub_cancel, Nat.reduceSub, mul_one]
    apply pred_mod_eq (k := 2)
    · rw [hn]; ring
    · have : 2 ^ a * (3 ^ b * 2) = 2 ^ (a + 1) * 3 ^ b := by ring
      omega

/-- `n + 1 = 2^a * (p + q - 1)` with `p ≠ q` primes, `5 ≤ p, q`: witness `x = 2^a * p * q`.
This is the Goldbach-type family. -/
theorem case_pow_two_mul_pq (n a p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hn : n + 2 = 2 ^ a * (p + q - 1) + 1) :
    A268597 n > 0 := by
  have hcop1 : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hcop : Nat.Coprime (2 ^ a) (p * q) := by
    apply Nat.Coprime.pow_left
    apply Nat.Coprime.mul_right
    · exact (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
    · exact (Nat.coprime_primes Nat.prime_two hq).2 (by omega)
  apply A268597_pos_of_witness (x := 2 ^ a * (p * q)) (by positivity)
  rw [Nat.totient_mul hcop, Nat.totient_mul hcop1, Nat.totient_prime hp, Nat.totient_prime hq]
  obtain ⟨A, rfl⟩ : ∃ A, p = A + 1 := ⟨p - 1, by omega⟩
  obtain ⟨B, rfl⟩ : ∃ B, q = B + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hn' : n + 1 = 2 ^ a * (A + B + 1) := by
    have : A + 1 + (B + 1) - 1 = A + B + 1 := by omega
    rw [this] at hn; omega
  rcases a with _ | a
  · simp only [pow_zero, one_mul, Nat.totient_one] at hn' ⊢
    apply pred_mod_eq (k := 1)
    · rw [hn']; ring
    · nlinarith
  · rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp only [Nat.add_sub_cancel, Nat.reduceSub, mul_one]
    apply pred_mod_eq (k := 2)
    · rw [hn']; ring
    · have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      have : 2 ^ (a + 1) * (A + B + 1) = 2 * (2 ^ a * (A + B + 1)) := by ring
      rw [this] at hn'
      -- need 2 (A + B + 1) ≤ A * B, i.e. (A-2)(B-2) ≥ 6 ; here A, B ≥ 4 distinct
      have hAB : 2 * (A + B + 1) ≤ A * B := by
        rcases Nat.lt_or_gt_of_ne (show A ≠ B by omega) with h | h
        · have h6 : 6 ≤ B := by
            have : B ≠ 5 := by
              rintro rfl
              have := hq.eq_one_or_self_of_dvd 2 (by norm_num); omega
            omega
          nlinarith
        · have h6 : 6 ≤ A := by
            have : A ≠ 5 := by
              rintro rfl
              have := hp.eq_one_or_self_of_dvd 2 (by norm_num); omega
            omega
          nlinarith
      nlinarith

/-- `n + 1 = 2^a`: witness `x = 2^(a+1)`. -/
theorem case_pow_two' (n a : ℕ) (hn : n + 1 = 2 ^ a) : A268597 n > 0 := by
  apply A268597_pos_of_witness (x := 2 ^ (a + 1)) (by positivity)
  rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
  simp only [Nat.add_sub_cancel, Nat.reduceSub, mul_one]
  apply pred_mod_eq (k := 1)
  · rw [pow_succ]; omega
  · omega

/-- The exact reduction: the conjecture follows from the following Goldbach-type statement:
every odd `M > 1` which is neither prime nor a power of `3` satisfies `M + 1 = p + q`
with distinct primes `p, q ≥ 5`. -/
theorem conjecture_of_goldbach
    (H : ∀ M : ℕ, Odd M → 1 < M → ¬ M.Prime → (∀ b, M ≠ 3 ^ b) →
      ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ 5 ≤ p ∧ 5 ≤ q ∧ p + q = M + 1) :
    ∀ n, A268597 n > 0 := by
  intro n
  obtain ⟨a, M, hM, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := n + 1) (by omega)
  by_cases hM1 : M = 1
  · subst hM1; exact case_pow_two' n a (by simpa using hn)
  have hM1' : 1 < M := by
    rcases hM with ⟨k, hk⟩; omega
  by_cases hMp : M.Prime
  · exact case_pow_two_mul_prime n a M hMp (by rintro rfl; exact absurd hM (by decide)) hn
  by_cases hM3 : ∃ b, M = 3 ^ b
  · obtain ⟨b, rfl⟩ := hM3
    have hb : 1 ≤ b := by
      rcases b with _ | b
      · simp at hM1
      · omega
    exact case_pow_two_mul_pow_three n a b hb hn
  push_neg at hM3
  obtain ⟨p, q, hp, hq, hpq, hp5, hq5, hsum⟩ := H M hM hM1' hMp hM3
  refine case_pow_two_mul_pq n a p q hp hq hpq hp5 hq5 ?_
  have : p + q - 1 = M := by omega
  rw [this]; omega

/--
A268597 Conjecture: a(n) > 0 for all n.
-/
theorem oeis_268597_conjecture_0 (n : ℕ) : A268597 n > 0 := by sorry

theorem oeis_268597_conjecture_0.disproof : ¬ (type_of% @oeis_268597_conjecture_0) := sorry
