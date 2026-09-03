import Submission.QuarterInterval
import Submission.Reduction

/-!
# The one-quarter bound for consecutive squarefree gaps

This connects the finite Roth-label counting argument to the exact gap sequence.
The all-positive-exponents conjecture is not assumed or proved here.
-/

open Filter Real

namespace SquarefreeGaps

lemma exists_gap_fourth_power_bound :
    ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, (seq (n+1) - seq n)^4 ≤ K^4 * seq n := by
  obtain ⟨H₀, hH₀⟩ := QuarterInterval.exists_squarefree_in_quarter_interval
  refine ⟨H₀ + 2, by omega, ?_⟩
  intro n
  let d := seq (n+1) - seq n
  change d^4 ≤ (H₀ + 2)^4 * seq n
  have hmono : seq n ≤ seq (n+1) := seq_strictMono.monotone (Nat.le_succ n)
  have hsum : seq (n+1) = seq n + d := by dsimp only [d]; omega
  by_cases hd : d ≤ H₀ + 2
  · calc
      d^4 ≤ (H₀ + 2)^4 := Nat.pow_le_pow_left hd 4
      _ ≤ (H₀ + 2)^4 * seq n := Nat.le_mul_of_pos_right _ (seq_pos n)
  · have hlt : (d - 1)^4 < seq n := by
      by_contra hc
      obtain ⟨q, hxq, hqle, hq⟩ := hH₀ (d-1) (by omega) (seq n)
        (Nat.le_of_not_gt hc)
      have hnext := next_le hq hxq
      omega
    have hdle : d ≤ 2 * (d - 1) := by omega
    have hK : 16 ≤ (H₀ + 2)^4 := by
      have := Nat.pow_le_pow_left (show 2 ≤ H₀ + 2 by omega) 4
      norm_num at this
      exact this
    calc
      d^4 ≤ (2 * (d-1))^4 := Nat.pow_le_pow_left hdle 4
      _ = 16 * (d-1)^4 := by ring
      _ ≤ 16 * seq n := Nat.mul_le_mul_left 16 hlt.le
      _ ≤ (H₀ + 2)^4 * seq n := Nat.mul_le_mul_right _ hK

lemma exists_gap_quarter_bound :
    ∃ C > (0 : ℝ), ∀ n : ℕ,
      (seq (n+1) - seq n : ℝ) ≤ C * (seq n : ℝ)^((1 : ℝ)/4) := by
  obtain ⟨K, hK, hbound⟩ := exists_gap_fourth_power_bound
  refine ⟨(K : ℝ), by exact_mod_cast hK, ?_⟩
  intro n
  have hcast : (seq (n+1) - seq n : ℝ)^4 ≤ (K : ℝ)^4 * (seq n : ℝ) := by
    rw [← Nat.cast_sub (seq_strictMono.monotone (Nat.le_succ n))]
    exact_mod_cast hbound n
  have hroot : ((seq n : ℝ)^((1 : ℝ)/4))^4 = (seq n : ℝ) := by
    simpa only [one_div] using
      (Real.rpow_inv_natCast_pow (n := 4) (Nat.cast_nonneg (seq n)) (by decide))
  apply le_of_pow_le_pow_left₀ (n := 4) (by decide) (by positivity)
  rwa [mul_pow, hroot]

/-- The requested gap estimate holds for every exponent at least one quarter. -/
lemma gapBound_of_quarter_le {ε : ℝ} (hε : (1 : ℝ)/4 ≤ ε) : GapBound ε := by
  obtain ⟨C, hC, hbound⟩ := exists_gap_quarter_bound
  apply Asymptotics.isBigO_iff'.mpr
  refine ⟨C, hC, Filter.Eventually.of_forall ?_⟩
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (gap_nonneg n), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact (hbound n).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast seq_pos n) hε) hC.le)

#print axioms exists_gap_fourth_power_bound
#print axioms gapBound_of_quarter_le

end SquarefreeGaps
