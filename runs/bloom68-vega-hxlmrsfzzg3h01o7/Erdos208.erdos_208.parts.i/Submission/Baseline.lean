import Submission.Elementary
import Submission.Reduction

/-!
# An unconditional one-third exponent for squarefree gaps

This development combines the elementary finite sieve with the exact enumeration
lemmas. It is a partial result only, and does not assume either target theorem.
-/

open Filter Real

namespace SquarefreeGaps

lemma gap_cube_le (n : ℕ) :
    (seq (n+1) - seq n)^3 ≤ 134217728 * seq n := by
  let d := seq (n+1) - seq n
  change d^3 ≤ 134217728 * seq n
  have heq : seq (n+1) = seq n + d := by
    dsimp only [d]
    have hm : seq n ≤ seq (n+1) := seq_strictMono.monotone (Nat.le_succ n)
    omega
  by_cases hd : d < 512
  · have hpow := Nat.pow_le_pow_left (Nat.le_of_lt hd) 3
    have hpos := seq_pos n
    norm_num at hpow
    nlinarith
  · let h := d / 16
    have hquot : 16 * h ≤ d ∧ d < 16 * (h+1) := by
      dsimp only [h]
      omega
    have hh : 32 ≤ h := by omega
    have hinside : 8 * h < d := by omega
    have hfail : h^3 < 8 * (seq n + 8*h) := by
      by_contra hc
      obtain ⟨q, hxq, hqle, hsq⟩ :=
        ElementarySquarefree.exists_squarefree_in_short_interval (seq n) h
          (by omega) (Nat.le_of_not_gt hc)
      have hnext := next_le hsq hxq
      omega
    have hsq : 128 ≤ h^2 := by nlinarith
    have hcub := Nat.mul_le_mul_right h hsq
    have hbase : h^3 ≤ 16 * seq n := by nlinarith
    have hdle : d ≤ 32 * h := by omega
    have hdPow := Nat.pow_le_pow_left hdle 3
    nlinarith

lemma gap_le_cuberoot (n : ℕ) :
    (seq (n+1) - seq n : ℝ) ≤ 512 * (seq n : ℝ)^((1 : ℝ)/3) := by
  have hcast : (seq (n+1) - seq n : ℝ)^3 ≤ 134217728 * (seq n : ℝ) := by
    rw [← Nat.cast_sub (seq_strictMono.monotone (Nat.le_succ n))]
    exact_mod_cast gap_cube_le n
  have hroot : ((seq n : ℝ)^((1 : ℝ)/3))^3 = (seq n : ℝ) := by
    simpa only [one_div] using
      (Real.rpow_inv_natCast_pow (n := 3) (Nat.cast_nonneg (seq n)) (by decide))
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by positivity)
  rw [mul_pow, hroot]
  norm_num
  exact hcast

/-- The conjectured bound holds unconditionally for every exponent at least one third. -/
lemma gapBound_of_third_le {ε : ℝ} (hε : (1 : ℝ)/3 ≤ ε) : GapBound ε := by
  apply Asymptotics.isBigO_iff'.mpr
  refine ⟨512, by norm_num, Filter.Eventually.of_forall ?_⟩
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (gap_nonneg n), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact (gap_le_cuberoot n).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast seq_pos n) hε) (by norm_num))

#print axioms gap_cube_le
#print axioms gapBound_of_third_le

end SquarefreeGaps
