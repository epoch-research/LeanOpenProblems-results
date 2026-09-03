import Submission.RowRemainderBounds

/-!
# A GCD condition sufficient for Erdős 68

Let `F n` be the sum of the individual floors of `n! / (k! - 1)`,
for `2 ≤ k ≤ n`. If the original series is rational, then
`gcd (F n) n! / n` tends to zero. Thus arbitrarily large indices
with `n ≤ gcd (F n) n!` would suffice to prove irrationality.

This file does not establish that infinite arithmetic condition.
-/

namespace RowGcdCriterion

open Erdos68Development Filter
open scoped Topology

def rowGcd (n : ℕ) : ℕ := Int.gcd (rowFloor n) (n.factorial : ℤ)

lemma rowGcd_pos (n : ℕ) : 0 < rowGcd n := by
  apply Int.gcd_pos_of_ne_zero_right
  exact_mod_cast Nat.factorial_ne_zero n

/-- Rationality gives a bound at every index, without requiring the
rational denominator to divide the factorial. -/
lemma rowGcd_le_den_mul_tail (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) (n : ℕ) :
    (rowGcd n : ℝ) ≤ (q.den : ℝ) * rowTail n := by
  let d : ℤ := q.num * (n.factorial : ℤ) - (q.den : ℤ) * rowFloor n
  have he : (d : ℝ) = (q.den : ℝ) * rowTail n := by
    dsimp [d, rowTail]
    rw [hq, Rat.cast_def]
    push_cast
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    field_simp
  have hd : 0 < d := by
    have h : (0 : ℝ) < d := by
      rw [he]
      exact mul_pos (by exact_mod_cast q.pos) (rowTail_pos n)
    exact_mod_cast h
  have hdiv : (rowGcd n : ℤ) ∣ d := by
    apply dvd_sub
    · exact dvd_mul_of_dvd_right (Int.gcd_dvd_right (rowFloor n) (n.factorial : ℤ)) _
    · exact dvd_mul_of_dvd_right (Int.gcd_dvd_left (rowFloor n) (n.factorial : ℤ)) _
  have hle : (rowGcd n : ℤ) ≤ d := Int.le_of_dvd hd hdiv
  have hle' : (rowGcd n : ℝ) ≤ (d : ℝ) := by exact_mod_cast hle
  rwa [he] at hle'

theorem rowGcd_div_self_tendsto_zero_of_rational (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) :
    Tendsto (fun n : ℕ => (rowGcd n : ℝ) / n) atTop (𝓝 0) := by
  apply squeeze_zero (g := fun n => (q.den : ℝ) * (rowTail n / n))
  · intro n
    positivity
  · intro n
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right (rowGcd_le_den_mul_tail q hq n) (Nat.cast_nonneg n)
  · simpa using RowRemainderBounds.rowTail_div_self_tendsto.const_mul (q.den : ℝ)

/-- The infinite GCD hypothesis here has not been proved for this sequence. -/
theorem irrational_of_frequently_large_rowGcd
    (h : ∀ N : ℕ, ∃ n ≥ N, n ≤ rowGcd n) :
    Irrational (∑' k : ℕ, term k) := by
  intro ⟨q, hq⟩
  have ht := rowGcd_div_self_tendsto_zero_of_rational q hq.symm
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  obtain ⟨n, hn, hg⟩ := h (max N 1)
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hgr : (n : ℝ) ≤ rowGcd n := by exact_mod_cast hg
  have hl : (1 : ℝ) ≤ (rowGcd n : ℝ) / n := (le_div_iff₀ hnp).mpr (by simpa)
  exact (not_lt_of_ge hl) (hN n hnN)

end RowGcdCriterion

#print axioms RowGcdCriterion.rowGcd_div_self_tendsto_zero_of_rational
#print axioms RowGcdCriterion.irrational_of_frequently_large_rowGcd
