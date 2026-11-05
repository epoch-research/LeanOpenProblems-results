import FormalConjecturesUtil

/-!
# An elementary form of the two-prime strip condition

This file records the exact connection between a prime value of an irrational
Beatty sequence at a prime index and a one-sided interval containing two primes.
-/

namespace Erdos972

/-- For an irrational slope, a prime Beatty value at a prime index is precisely
    a pair of primes within the one-sided strip `0 < α * p - q < 1`. -/
theorem prime_floor_iff_prime_strip (α : ℝ) (hα : 0 < α)
    (hI : Irrational α) (p : ℕ) (hp : p.Prime) :
    (Nat.floor (α * (p : ℝ))).Prime ↔
      ∃ q : ℕ, q.Prime ∧
        0 < α * (p : ℝ) - (q : ℝ) ∧
        α * (p : ℝ) - (q : ℝ) < 1 := by
  constructor
  · intro hq
    let q : ℕ := Nat.floor (α * (p : ℝ))
    have hx : 0 ≤ α * (p : ℝ) := mul_nonneg hα.le (Nat.cast_nonneg _)
    have hle : (q : ℝ) ≤ α * (p : ℝ) := Nat.floor_le hx
    have hne : α * (p : ℝ) ≠ (q : ℝ) := (hI.mul_natCast hp.ne_zero).ne_nat q
    have hlt : (q : ℝ) < α * (p : ℝ) := lt_of_le_of_ne hle hne.symm
    have hu : α * (p : ℝ) < (q : ℝ) + 1 := Nat.lt_floor_add_one _
    exact ⟨q, hq, by linarith, by linarith⟩
  · rintro ⟨q, hq, hlo, hhi⟩
    have hx : 0 ≤ α * (p : ℝ) := by
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
      linarith
    have heq : Nat.floor (α * (p : ℝ)) = q :=
      (Nat.floor_eq_iff hx).2 (by constructor <;> linarith)
    simpa only [heq] using hq

end Erdos972
