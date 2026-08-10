import FormalConjectures.Util.ProblemImports

open Nat

/--
A007918: Least prime $\ge n$ (version 1 of the "next prime" function).
-/
noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

/-!
## Analysis of the conjecture

Write `B(n) = n ^ (n ^ (1/n))`.  A precise asymptotic expansion gives
`B(n) - n = (log n)^2 + (log n)^3 (log n + 1) / (2 n) + ... = (log n)^2 + o(1)`,
so `B(n)` is `n` plus essentially `(log n)^2`.

Since `a n` is the least prime `≥ n`, for `n` lying just above a prime `p`
(the binding case `n = p + 1`) the inequality `a n < B(n)` is equivalent to
`(next prime after p) - p < (log p)^2 + 1`, i.e. to the bound
`gap(p) < (log p)^2` on prime gaps.  This is exactly **Cramér's conjecture**.

It is an open problem, strictly stronger than the Riemann Hypothesis: even under
RH one only gets `gap(p) ≪ √p · log p`, and unconditionally only
`gap(p) ≪ p^{0.525}` (Baker–Harman–Pintz), both vastly larger than `(log p)^2`.
No counterexample is known either (the maximal Cramér–Shanks–Granville ratio
`gap/(log p)^2` is `0.9206 < 1`, verified for all `p` up to `5.5·10^18`), and the
negation is likewise unprovable (the best lower bounds on large gaps are
`o((log p)^2)`).  Mathlib's strongest tool here is Bertrand's postulate
(`a n < 2 n`), but `B(n) < 2 n` for every `n`, so it does not suffice.

Below we record the genuinely provable content and isolate the open core.
-/

/-- `a n` is prime and is `≥ n`. -/
theorem a_spec (n : ℕ) : Nat.Prime (a n) ∧ n ≤ a n := by
  unfold a
  exact Nat.find_spec (p := fun p => Nat.Prime p ∧ n ≤ p) _

/-- When `n` itself is prime, `a n = n`. -/
theorem a_eq_of_prime {n : ℕ} (hp : Nat.Prime n) : a n = n := by
  unfold a
  apply le_antisymm
  · exact Nat.find_min' (p := fun p => Nat.Prime p ∧ n ≤ p) _ ⟨hp, le_rfl⟩
  · exact (Nat.find_spec (p := fun p => Nat.Prime p ∧ n ≤ p) _).2

/-- General computation rule for `a`: if `q` is prime, `n ≤ q`, and no integer in
`[n, q)` is prime, then `a n = q`.  Together with `verify_step` this gives a fully
decidable procedure proving `a n < B(n)` for any individual `n`. -/
theorem a_eq (n q : ℕ) (hq : Nat.Prime q) (hnq : n ≤ q)
    (hmin : ∀ m, n ≤ m → m < q → ¬ Nat.Prime m) : a n = q := by
  apply le_antisymm
  · unfold a; exact Nat.find_min' (p := fun p => Nat.Prime p ∧ n ≤ p) _ ⟨hq, hnq⟩
  · by_contra h
    push_neg at h
    exact hmin (a n) (a_spec n).2 h (a_spec n).1

/-- Key inequality `n < n ^ (n ^ (1/n))` for `n > 1`: the base `n > 1` raised to an
exponent `n ^ (1/n) > 1` exceeds `n = n ^ 1`.  This settles the case `n` prime. -/
theorem lt_rpow_self (n : ℕ) (h_n : 1 < n) :
    (n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h_n
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hexp : (1 : ℝ) < (n : ℝ) ^ (1 / (n : ℝ)) := by
    rw [Real.one_lt_rpow_iff_of_pos hn0]
    exact Or.inl ⟨hn1, by positivity⟩
  calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
        rw [Real.rpow_lt_rpow_left_iff hn1]; exact hexp

/-- Sharp provable lower bound `B(n) ≥ n + (log n)^2` for `n > 1`, where
`B(n) = n ^ (n ^ (1/n))`.  Proof: `n^(1/n) = exp((log n)/n) ≥ 1 + (log n)/n`, hence
`B(n) ≥ n^(1 + (log n)/n) = n · exp((log n)^2/n) ≥ n · (1 + (log n)^2/n) = n + (log n)^2`.
Consequently the conjecture for composite `n` is *equivalent* to the prime-gap bound
`a n < n + (log n)^2`, i.e. exactly **Cramér's conjecture** `gap(p) < (log p)^2`. -/
theorem add_log_sq_le_rpow_self (n : ℕ) (h_n : 1 < n) :
    (n : ℝ) + (Real.log n) ^ 2 ≤ (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h_n
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  -- Step A: n^(1/n) ≥ 1 + (log n)/n
  have hA : 1 + Real.log n / n ≤ (n : ℝ) ^ (1 / (n : ℝ)) := by
    rw [Real.rpow_def_of_pos hn0]
    have heq : Real.log n * (1 / (n : ℝ)) = Real.log n / n := by ring
    rw [heq]
    have := Real.add_one_le_exp (Real.log n / n)
    linarith
  -- Step B: monotonicity of x ↦ n^x for base n > 1
  have hB : (n : ℝ) ^ (1 + Real.log n / n) ≤ (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) :=
    (Real.rpow_le_rpow_left_iff hn1).mpr hA
  -- Step C: n^(1 + (log n)/n) ≥ n + (log n)^2
  have hC : (n : ℝ) + (Real.log n) ^ 2 ≤ (n : ℝ) ^ (1 + Real.log n / n) := by
    rw [Real.rpow_add hn0, Real.rpow_one]
    have hpow : (n : ℝ) ^ (Real.log n / n) = Real.exp ((Real.log n) ^ 2 / n) := by
      rw [Real.rpow_def_of_pos hn0]; congr 1; rw [sq]; ring
    rw [hpow]
    have hexp : 1 + (Real.log n) ^ 2 / n ≤ Real.exp ((Real.log n) ^ 2 / n) := by
      have := Real.add_one_le_exp ((Real.log n) ^ 2 / n); linarith
    have hid : (n : ℝ) * (1 + (Real.log n) ^ 2 / n) = (n : ℝ) + (Real.log n) ^ 2 := by
      field_simp
    calc (n : ℝ) + (Real.log n) ^ 2 = (n : ℝ) * (1 + (Real.log n) ^ 2 / n) := hid.symm
      _ ≤ (n : ℝ) * Real.exp ((Real.log n) ^ 2 / n) :=
          mul_le_mul_of_nonneg_left hexp (le_of_lt hn0)
  linarith

/-- **Verification engine.** For an individual `n`, the real-analytic inequality
`a n < B(n)` reduces to two *decidable integer* inequalities via a rational witness
`r = c/d`:  if `c^n ≤ n·d^n` (so `r ≤ n^(1/n)`) and `q^d < n^c` (so `q < n^r`), then
`a n = q < n^r ≤ n^(n^(1/n)) = B(n)`.  Hence `a n < B(n)` is finitely checkable for
every individual `n`.  Moreover such a witness exists **iff** `q < B(n)` (the window
`[log q / log n, n^(1/n)]` for `r` is nonempty iff the inequality holds), so the
conjecture is *exactly* the statement that witnesses exist for all `n` — which for the
tail is Cramér's conjecture.  (Even Bertrand's `q < 2n` fails to yield a witness for
large `n`, as it would require `n·log 2 < (log n)^2`.) -/
theorem verify_step (n c d q : ℕ) (hn : 1 < n) (hd : 0 < d)
    (hq : a n = q) (h1 : c ^ n ≤ n * d ^ n) (h2 : q ^ d < n ^ c) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  rw [hq]
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  set r : ℝ := (c : ℝ) / (d : ℝ) with hr
  have hr0 : 0 ≤ r := by positivity
  -- Step 1: `r ≤ n^(1/n)`, from `c^n ≤ n·d^n`.
  have hstep1 : r ≤ (n : ℝ) ^ (1 / (n : ℝ)) := by
    have hrn : r ^ (n : ℕ) ≤ (n : ℝ) := by
      rw [hr, div_pow, div_le_iff₀ (by positivity)]
      have : (c : ℝ) ^ n ≤ (n : ℝ) * (d : ℝ) ^ n := by exact_mod_cast h1
      exact this
    have hroot : r = (r ^ (n : ℕ) : ℝ) ^ (1 / (n : ℝ)) := by
      rw [← Real.rpow_natCast r n, ← Real.rpow_mul hr0, mul_one_div, div_self hn0.ne']
      simp [Real.rpow_one]
    rw [hroot]
    exact Real.rpow_le_rpow (by positivity) hrn (by positivity)
  -- Step 2: monotonicity of the exponent for base `n > 1`.
  have hstep2 : (n : ℝ) ^ r ≤ (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt hn1) hstep1
  -- Step 3: `q < n^r`, from `q^d < n^c`.
  have hstep3 : (q : ℝ) < (n : ℝ) ^ r := by
    have hpow : ((n : ℝ) ^ r) ^ (d : ℕ) = (n : ℝ) ^ (c : ℕ) := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ r) d, ← Real.rpow_mul (le_of_lt hn0), hr,
        div_mul_cancel₀ _ hd0.ne', Real.rpow_natCast]
    have hqd : (q : ℝ) ^ (d : ℕ) < ((n : ℝ) ^ r) ^ (d : ℕ) := by
      rw [hpow]; exact_mod_cast h2
    exact lt_of_pow_lt_pow_left₀ d (by positivity) hqd
  calc (q : ℝ) < (n : ℝ) ^ r := hstep3
    _ ≤ (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := hstep2

/-- **Reduction to Cramér's conjecture.** The full conjecture follows from the
prime‑gap bound `a n < n + (log n)^2` (a Cramér‑type statement: for the binding case
`n = p+1` it reads `gap(p) < (log(p+1))^2 + 1`).  Indeed `a n < n + (log n)^2 ≤ B(n)`,
where the second inequality is `add_log_sq_le_rpow_self`.  This isolates the *only*
unproven input as exactly Cramér's conjecture — the proof completes verbatim once such a
prime‑gap bound is available. -/
theorem conjecture_of_cramer
    (H : ∀ m : ℕ, 1 < m → (a m : ℝ) < (m : ℝ) + (Real.log m) ^ 2) :
    ∀ n : ℕ, 1 < n → (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  intro n hn
  calc (a n : ℝ) < (n : ℝ) + (Real.log n) ^ 2 := H n hn
    _ ≤ (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := add_log_sq_le_rpow_self n hn

/-- Composite-case wrapper for the verification engine: supply `q` prime, `n ≤ q`,
primality‑free interval `[n,q)`, and the two integer inequalities. -/
theorem step (n c d q : ℕ) (hn : 1 < n) (hd : 0 < d) (hq : Nat.Prime q) (hnq : n ≤ q)
    (hmin : ∀ m, n ≤ m → m < q → ¬ Nat.Prime m)
    (h1 : c ^ n ≤ n * d ^ n) (h2 : q ^ d < n ^ c) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) :=
  verify_step n c d q hn hd (a_eq n q hq hnq hmin) h1 h2

/-- Prime-case wrapper: `a n = n < B(n)`. -/
theorem step_prime (n : ℕ) (hn : 1 < n) (hp : Nat.Prime n) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  have h : (a n : ℝ) = (n : ℝ) := by rw [a_eq_of_prime hp]
  rw [h]; exact lt_rpow_self n hn

/-- **Rigorous finite verification.** The conjecture holds for every `n` with
`1 < n ≤ 30`, proved purely by the integer-witness engine (each composite `n` is
discharged from two integer inequalities; each prime `n` from `lt_rpow_self`).  This
exhibits the verification engine working at scale; the same procedure verifies any
finite range, with the witness denominators slowly growing as `n^(1/n) → 1`. -/
theorem oeis_7918_verified_le_30 (n : ℕ) (hn : 1 < n) (hle : n ≤ 30) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  interval_cases n
  · exact step_prime 2 (by norm_num) (by norm_num)
  · exact step_prime 3 (by norm_num) (by norm_num)
  · exact step 4 4 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step_prime 5 (by norm_num) (by norm_num)
  · exact step 6 4 3 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step_prime 7 (by norm_num) (by norm_num)
  · exact step 8 5 4 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step 9 5 4 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step 10 5 4 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step_prime 11 (by norm_num) (by norm_num)
  · exact step 12 6 5 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step_prime 13 (by norm_num) (by norm_num)
  · exact step 14 6 5 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step 15 7 6 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step 16 7 6 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step_prime 17 (by norm_num) (by norm_num)
  · exact step 18 7 6 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step_prime 19 (by norm_num) (by norm_num)
  · exact step 20 8 7 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step 21 8 7 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step 22 8 7 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step_prime 23 (by norm_num) (by norm_num)
  · exact step 24 9 8 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step 25 9 8 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step 26 9 8 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step 27 9 8 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step 28 9 8 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)
  · exact step_prime 29 (by norm_num) (by norm_num)
  · exact step 30 10 9 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by intro m h1 h2; interval_cases m <;> norm_num) (by norm_num) (by norm_num)

/--
Conjecture: if n > 1, then a(n) < n^(n^(1/n)). - _Thomas Ordowski_, Feb 23 2023
-/
theorem oeis_7918_conjecture_1 (n : ℕ) (h_n : 1 < n) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  by_cases hp : Nat.Prime n
  · -- `n` prime: `a n = n`, and `n < B(n)` by `lt_rpow_self`.
    exact step_prime n h_n hp
  · by_cases hle : n ≤ 30
    · -- small `n`: rigorous finite verification.
      exact oeis_7918_verified_le_30 n h_n hle
    · -- `n` composite with `n > 30`: by `verify_step` it suffices to produce integer
      -- witnesses `c, d` with `c^n ≤ n·d^n` and `(a n)^d < n^c`.  Such witnesses exist
      -- for a given `n` iff `a n < B(n)`, i.e. iff the next prime after `n` is
      -- `< n + (log n)^2(1+o(1))`.  Over all `n` this is exactly **Cramér's conjecture**
      -- on prime gaps (open since 1936, stronger than RH): the best unconditional bound
      -- is the polynomial `p^{0.525}`, while `B(n) - n ~ (log n)^2`, so no provable
      -- prime-gap result places a prime in the interval `[n, B(n))`.
      sorry
