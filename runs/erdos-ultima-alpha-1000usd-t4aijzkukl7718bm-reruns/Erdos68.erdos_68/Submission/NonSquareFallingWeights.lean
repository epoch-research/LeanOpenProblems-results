import Submission.Development

/-!
Positive falling-factorial weights for the factorial-power columns.
These estimates do not construct integer forms for the original sum.
-/

namespace NonSquareFallingWeights

noncomputable def weight (N r n : ℕ) : ℝ :=
  (n.descFactorial N : ℝ) ^ (r + 1) / ((n + 2).factorial : ℝ) ^ (r + 1)

lemma weight_nonneg (N r n : ℕ) : 0 ≤ weight N r n := by
  unfold weight
  positivity

lemma weight_zero (N r n : ℕ) (hn : n < N) : weight N r n = 0 := by
  simp [weight, Nat.descFactorial_of_lt hn]

lemma weight_shift (N r k : ℕ) :
    weight N r (N + k) =
      (1 / ((N + k + 2 : ℝ) * (N + k + 1) * (k.factorial : ℝ))) ^ (r + 1) := by
  have hd : (0 : ℝ) < (N + k).descFactorial N := by
    exact_mod_cast Nat.descFactorial_pos.mpr (show N ≤ N + k by omega)
  have hk : (0 : ℝ) < k.factorial := by positivity
  have hf : (k.factorial : ℝ) * (N + k).descFactorial N = (N + k).factorial := by
    exact_mod_cast (show k.factorial * (N + k).descFactorial N = (N + k).factorial by
      simpa using Nat.factorial_mul_descFactorial (show N ≤ N + k by omega))
  have hf2 : ((N + k + 2).factorial : ℝ) =
      (N + k + 2 : ℝ) * (N + k + 1) *
        ((k.factorial : ℝ) * (N + k).descFactorial N) := by
    rw [hf, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  unfold weight
  rw [← div_pow, hf2]
  congr 1
  have h1 : (N + k + 1 : ℝ) ≠ 0 := by positivity
  have h2 : (N + k + 2 : ℝ) ≠ 0 := by positivity
  field_simp

lemma weight_shift_le (N r k : ℕ) :
    weight N r (N + k) ≤
      (1 / ((N + 2 : ℝ) * (N + 1))) ^ (r + 1) * (1 / (k.factorial : ℝ)) := by
  have hk : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hp : (k.factorial : ℝ) ≤ (k.factorial : ℝ) ^ (r + 1) := by
    simpa using pow_le_pow_right₀ hk (show 1 ≤ r + 1 by omega)
  rw [weight_shift, ← div_div, div_pow]
  calc
    (1 / ((N + k + 2 : ℝ) * (N + k + 1))) ^ (r + 1) /
        (k.factorial : ℝ) ^ (r + 1) ≤
      (1 / ((N + 2 : ℝ) * (N + 1))) ^ (r + 1) / (k.factorial : ℝ) := by
        gcongr <;> nlinarith [Nat.cast_nonneg (α := ℝ) k]
    _ = _ := by ring


lemma summable_weight (N r : ℕ) : Summable (weight N r) := by
  have hs : Summable (fun k : ℕ => 1 / (k.factorial : ℝ)) := by
    simpa only [one_pow] using Real.summable_pow_div_factorial 1
  have ht : Summable (fun k : ℕ => weight N r (N + k)) :=
    (hs.mul_left ((1 / ((N + 2 : ℝ) * (N + 1))) ^ (r + 1))).of_nonneg_of_le
      (fun k => weight_nonneg N r (N + k)) (weight_shift_le N r)
  exact (summable_nat_add_iff N).mp (by simpa only [Nat.add_comm] using ht)

lemma tsum_weight_eq_shift (N r : ℕ) :
    (∑' n : ℕ, weight N r n) = ∑' k : ℕ, weight N r (N + k) := by
  have h := (summable_weight N r).sum_add_tsum_nat_add N
  have hz : (∑ n ∈ Finset.range N, weight N r n) = 0 :=
    Finset.sum_eq_zero (fun n hn => weight_zero N r n (Finset.mem_range.mp hn))
  rw [hz, zero_add] at h
  simpa only [Nat.add_comm] using h.symm

/-- The positivity estimate is on natural-number nodes, not a square
factorization over all real inputs. It supplies no common integral leading
coefficient for the original sum. -/
theorem weight_sum_bounds (N r : ℕ) :
    0 < (∑' n : ℕ, weight N r n) ∧
      (∑' n : ℕ, weight N r n) <
        3 / (((N + 2 : ℝ) * (N + 1)) ^ (r + 1)) := by
  constructor
  · apply (summable_weight N r).tsum_pos (weight_nonneg N r) N
    unfold weight
    rw [Nat.descFactorial_self]
    positivity
  · have he : HasSum (fun k : ℕ => 1 / (k.factorial : ℝ)) (Real.exp 1) := by
      simpa only [one_pow, ← Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (1 : ℝ))
    have hs : Summable (fun k => weight N r (N + k)) := by
      simpa only [Nat.add_comm] using (summable_nat_add_iff N).mpr (summable_weight N r)
    have hb := Summable.tsum_le_tsum (weight_shift_le N r) hs
      (he.summable.mul_left ((1 / ((N + 2 : ℝ) * (N + 1))) ^ (r + 1)))
    rw [tsum_mul_left, he.tsum_eq] at hb
    rw [tsum_weight_eq_shift]
    apply hb.trans_lt
    calc
      (1 / ((N + 2 : ℝ) * (N + 1))) ^ (r + 1) * Real.exp 1 <
          (1 / ((N + 2 : ℝ) * (N + 1))) ^ (r + 1) * 3 :=
        mul_lt_mul_of_pos_left Real.exp_one_lt_three (by positivity)
      _ = _ := by rw [div_pow, one_pow]; ring

open Filter
open scoped Topology

lemma tendsto_weight_sum (r : ℕ) :
    Tendsto (fun N : ℕ => ∑' n : ℕ, weight N r n) atTop (𝓝 0) := by
  have hg : Tendsto (fun N : ℕ => 3 / (N + 1 : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).const_mul (3 : ℝ)
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_zero, mul_one_div] using h
  apply squeeze_zero (fun N => (weight_sum_bounds N r).1.le) _ hg
  intro N
  apply (weight_sum_bounds N r).2.le.trans
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hb : (1 : ℝ) ≤ (N + 2) * (N + 1) := by nlinarith
  have hp : (N + 2 : ℝ) * (N + 1) ≤ ((N + 2 : ℝ) * (N + 1)) ^ (r + 1) := by
    simpa using pow_le_pow_right₀ hb (show 1 ≤ r + 1 by omega)
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)


noncomputable def originalWeight (N n : ℕ) : ℝ :=
  (n.descFactorial N : ℝ) * Erdos68Development.term n

lemma originalWeight_nonneg (N n : ℕ) : 0 ≤ originalWeight N n := by
  exact mul_nonneg (Nat.cast_nonneg _) (Erdos68Development.term_pos n).le

lemma originalWeight_le (N n : ℕ) : originalWeight N n ≤ 2 * weight N 0 n := by
  calc
    originalWeight N n ≤ (n.descFactorial N : ℝ) * (2 / ((n + 2).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (Erdos68Development.term_le_factorial n) (Nat.cast_nonneg _)
    _ = 2 * weight N 0 n := by simp only [weight, zero_add, pow_one]; ring

lemma summable_originalWeight (N : ℕ) : Summable (originalWeight N) :=
  ((summable_weight N 0).mul_left 2).of_nonneg_of_le
    (originalWeight_nonneg N) (originalWeight_le N)

lemma originalWeight_sum_le (N : ℕ) :
    (∑' n : ℕ, originalWeight N n) ≤ 2 * (∑' n : ℕ, weight N 0 n) := by
  simpa only [tsum_mul_left] using Summable.tsum_le_tsum (originalWeight_le N)
    (summable_originalWeight N) ((summable_weight N 0).mul_left 2)

/-- Positive weighted sums of the original rows tend to zero. They have not
been expressed as integer linear forms in the unweighted sum. -/
theorem originalWeight_sum_bounds (N : ℕ) :
    0 < (∑' n : ℕ, originalWeight N n) ∧
      (∑' n : ℕ, originalWeight N n) < 6 / ((N + 2 : ℝ) * (N + 1)) := by
  constructor
  · apply (summable_originalWeight N).tsum_pos (originalWeight_nonneg N) N
    unfold originalWeight
    rw [Nat.descFactorial_self]
    exact mul_pos (by positivity) (Erdos68Development.term_pos N)
  · calc
      (∑' n : ℕ, originalWeight N n) ≤ 2 * (∑' n : ℕ, weight N 0 n) :=
        originalWeight_sum_le N
      _ < 2 * (3 / ((N + 2 : ℝ) * (N + 1))) :=
        mul_lt_mul_of_pos_left (by simpa only [zero_add, pow_one] using (weight_sum_bounds N 0).2)
          (by norm_num)
      _ = _ := by ring

lemma tendsto_originalWeight_sum :
    Tendsto (fun N : ℕ => ∑' n : ℕ, originalWeight N n) atTop (𝓝 0) := by
  have h := (tendsto_weight_sum 0).const_mul (2 : ℝ)
  simp only [mul_zero] at h
  exact squeeze_zero (fun N => (originalWeight_sum_bounds N).1.le) originalWeight_sum_le h

end NonSquareFallingWeights

#print axioms NonSquareFallingWeights.weight_sum_bounds
#print axioms NonSquareFallingWeights.tendsto_weight_sum

#print axioms NonSquareFallingWeights.originalWeight_sum_bounds
#print axioms NonSquareFallingWeights.tendsto_originalWeight_sum
