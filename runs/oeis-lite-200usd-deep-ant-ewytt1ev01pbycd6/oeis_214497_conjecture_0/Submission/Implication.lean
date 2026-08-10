import FormalConjectures.Util.ProblemImports

open Nat

/-- The exact conjecture statement from `Spec.lean`, as a hypothesis. -/
abbrev A214497Stmt : Prop :=
  ∀ (n : ℕ), n > 0 →
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

/-- The (open) twin prime conjecture: arbitrarily large twin primes. -/
abbrev TwinPrimes : Prop := ∀ N : ℕ, ∃ p : ℕ, p > N ∧ p.Prime ∧ (p + 2).Prime

/-- **Key fact (machine-checked):** the A214497 conjecture *implies* the twin
prime conjecture.  Hence any proof of `oeis_214497_conjecture_0` would prove the
twin prime conjecture, which is open; so the statement is not provable from
current mathematics, and (being true on every tested `n`) its negation is not
provable either. -/
theorem A214497_implies_twin_primes (H : A214497Stmt) : TwinPrimes := by
  intro N
  -- Apply the conjecture at n = N + 1 (which is > 0).
  obtain ⟨k, h1, h2⟩ := H (N + 1) (Nat.succ_pos N)
  set m : ℕ := 3 ^ (N + 1) - k with hm
  -- The center value a = m * 2^(N+1).
  set a : ℕ := m * 2 ^ (N + 1) with ha
  -- First, m ≥ 1: otherwise a = 0 and `m*2^(N+1) - 1 = 0`, but `Nat.Prime 0` is false.
  have hmpos : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      have hazero : a = 0 := by rw [ha, h, Nat.zero_mul]
      rw [hazero] at h1
      simp only [Nat.zero_sub] at h1
      exact Nat.not_prime_zero h1
    · exact h
  -- 2^(N+1) ≥ N + 2, hence a ≥ 2^(N+1) ≥ N + 2.
  have hpow : N + 1 < 2 ^ (N + 1) := Nat.lt_two_pow_self
  have ha_ge : a ≥ 2 ^ (N + 1) := by
    have : a = m * 2 ^ (N + 1) := rfl
    calc a = m * 2 ^ (N + 1) := rfl
      _ ≥ 1 * 2 ^ (N + 1) := by exact Nat.mul_le_mul_right _ hmpos
      _ = 2 ^ (N + 1) := one_mul _
  have ha_big : a ≥ N + 2 := le_trans (by omega) ha_ge
  -- The twin prime witness is p = a - 1.
  refine ⟨a - 1, ?_, h1, ?_⟩
  · -- p = a - 1 > N
    omega
  · -- p + 2 = a + 1, and `Nat.Prime (a + 1)` is exactly `h2`.
    have : a - 1 + 2 = a + 1 := by omega
    rw [this]
    exact h2
