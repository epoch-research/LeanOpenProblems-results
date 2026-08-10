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

/-- `a n` is prime. -/
lemma a_prime (n : ℕ) : Nat.Prime (a n) :=
  (Nat.find_spec (p := fun p => Nat.Prime p ∧ n ≤ p) _).1

/-- `a n ≥ n`. -/
lemma a_ge (n : ℕ) : n ≤ a n :=
  (Nat.find_spec (p := fun p => Nat.Prime p ∧ n ≤ p) _).2

/-- If `n` is prime then `a n = n`. -/
lemma a_of_prime {n : ℕ} (hn : Nat.Prime n) : a n = n :=
  le_antisymm (Nat.find_le ⟨hn, le_refl n⟩) (a_ge n)

/-- The bound `n ^ (n ^ (1/n))` is strictly larger than `n` (for `n > 1`). -/
lemma rhs_gt (n : ℕ) (h : 1 < n) : (n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have he : (1 : ℝ) < (n : ℝ) ^ (1 / (n : ℝ)) := by
    rw [Real.one_lt_rpow_iff_of_pos hnpos]; exact Or.inl ⟨hn1, by positivity⟩
  calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := (Real.rpow_lt_rpow_left_iff hn1).mpr he

/--
Conjecture: if n > 1, then a(n) < n^(n^(1/n)). - _Thomas Ordowski_, Feb 23 2023

Mathematical analysis of this statement.

Writing `B(n) = n^(n^(1/n))`, an elementary computation (since `e^x - 1 > x`) gives
`B(n) > n + (log n)^2` for all `n > 1`, while the precise asymptotics are
`B(n) - n = (log n)^2 + ((log n)^4 + (log n)^3)/(2n) + …`, so `B(n) - n ~ (log n)^2`
and `B(n)/n → 1` (in fact `B(n)/n ≤ 1.866 < 2` for every `n`).

Consequently the statement `a(n) < B(n)` for composite `n` is *equivalent* to the
assertion that the interval `[n, n + (log n)^2)` contains a prime, i.e. to a
**Cramér-type prime-gap bound** `p_{k+1} - p_k ≲ (log p_k)^2`. This is an open problem,
strictly stronger than the Riemann Hypothesis: the strongest unconditional results give
only a prime in `[n, n + n^{0.525}]` (Baker–Harman–Pintz), and even RH yields only
`O(√n log n)` gaps — both far larger than `(log n)^2`. (Mathlib currently provides only
Bertrand's postulate, a prime in `(n, 2n)`, which is insufficient since `B(n) < 2n`.)

The statement is verified true for every `n` up to the full table of maximal prime gaps
(beyond `10^18`; the maximal Cramér–Shanks–Granville ratio is `0.9206 < 1`), so no
counterexample is known or constructible. Hence the conjecture can neither be proved nor
disproved with current mathematics.

The proof below settles the case where `n` is prime completely (then `a n = n < B(n)`),
and reduces the remaining (composite) case to exactly the open prime-gap statement above.
-/
theorem oeis_7918_conjecture_1 (n : ℕ) (h_n : 1 < n) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  by_cases hp : Nat.Prime n
  · -- `n` prime: `a n = n`, and `n < B(n)`.
    rw [a_of_prime hp]; exact rhs_gt n h_n
  · -- `n` composite: `a n` is the least prime `> n`; the bound `a n < B(n) ~ n + (log n)^2`
    -- is a Cramér-type prime-gap estimate, an open problem (see the docstring above).
    sorry
