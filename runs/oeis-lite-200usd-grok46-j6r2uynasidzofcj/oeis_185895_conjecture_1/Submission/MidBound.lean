import FormalConjectures.Util.ProblemImports

open Real

lemma stirlingSeq_antitone_ge_one {n : ℕ} (hn : 1 ≤ n) :
    Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
  cases n with
  | zero => omega
  | succ n =>
    have h := Stirling.stirlingSeq'_antitone (Nat.zero_le n)
    simpa [Function.comp] using h

lemma factorial_upper_stirling (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n := by
  have hseq : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 :=
    stirlingSeq_antitone_ge_one hn
  rw [Stirling.stirlingSeq_one] at hseq
  unfold Stirling.stirlingSeq at hseq
  have hpos : (0 : ℝ) < Real.sqrt (2 * n) * ((n : ℝ) / Real.exp 1) ^ n := by
    positivity
  rw [div_le_iff₀ hpos] at hseq
  refine le_trans hseq ?_
  have hsq : Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt (n : ℝ) :=
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2) (n : ℝ)
  rw [hsq]
  have hs2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  field_simp
  simp

lemma log_factorial_upper {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤
      1 + Real.log n / 2 + n * Real.log n - n := by
  have hpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hle := factorial_upper_stirling n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have harg : (0 : ℝ) < Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n := by
    positivity
  have := Real.log_le_log hpos hle
  refine le_trans this ?_
  have h1 : Real.log (Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n) =
      1 + Real.log n / 2 + n * (Real.log n - 1) := by
    have he : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    have hs : Real.log (Real.sqrt (n : ℝ)) = Real.log n / 2 :=
      Real.log_sqrt (le_of_lt hn0)
    have hp : Real.log (((n : ℝ) / Real.exp 1) ^ n) =
        n * Real.log ((n : ℝ) / Real.exp 1) :=
      Real.log_pow _ n
    have hd : Real.log ((n : ℝ) / Real.exp 1) = Real.log n - 1 := by
      rw [Real.log_div (ne_of_gt hn0) (Real.exp_ne_zero 1), Real.log_exp]
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), he, hs, hp, hd]
  rw [h1]
  linarith

#check log_factorial_upper
