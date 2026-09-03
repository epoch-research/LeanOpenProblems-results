import Submission.SelfCenteredLog

/-! Partial summation for nonlinear Lipschitz functions of the logarithm.
Endpoint centering avoids demanding a logarithmic rate in a mean-value theorem. -/
namespace Erdos972LipschitzLogWeights

open Finset Filter
open scoped Topology
open Erdos972SelfCenteredLog Erdos972ExponentialSum

lemma abs_weighted_prefix (w z : ℕ → ℝ) (N : ℕ) (E A V : ℝ)
    (hE : ∀ j ≤ N, |∑ n ∈ range j, z n| ≤ E)
    (hA : |w (N-1)| ≤ A)
    (hV : (∑ n ∈ range (N-1), |w (n+1)-w n|) ≤ V) :
    |∑ n ∈ range N, w n*z n| ≤ (A+V)*E := by
  have hE0 : 0 ≤ E := by simpa using hE 0 (Nat.zero_le N)
  have he := sum_range_by_parts w z N
  simp only [smul_eq_mul] at he
  rw [he]
  calc
    _ ≤ |w (N-1)*(∑ n ∈ range N, z n)| +
        |∑ n ∈ range (N-1), (w (n+1)-w n)*(∑ i ∈ range (n+1), z i)| := abs_sub _ _
    _ ≤ A*E+(∑ n ∈ range (N-1), |w (n+1)-w n|)*E := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul hA (hE N le_rfl) (abs_nonneg _) ((abs_nonneg _).trans hA)
      · rw [sum_mul]
        apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro n hn
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hE (n+1) (by have := mem_range.mp hn; omega)) (abs_nonneg _)
    _ ≤ (A+V)*E := by
      have hh := mul_le_mul_of_nonneg_right hV hE0
      nlinarith only [hh]

lemma logarithmic_variation_bound (Φ : ℝ → ℝ) {L : ℝ} (_hL : 0 ≤ L)
    (hΦ : ∀ x y, |Φ x-Φ y| ≤ L*|x-y|) (N : ℕ) :
    (∑ n ∈ range (N-1), |Φ (Real.log (n+2 : ℕ))-Φ (Real.log (n+1 : ℕ))|) ≤
      L*Real.log N := by
  by_cases hN : N = 0
  · simp [hN]
  calc
    _ ≤ ∑ n ∈ range (N-1), L*(Real.log (n+2 : ℕ)-Real.log (n+1 : ℕ)) := by
      apply sum_le_sum
      intro n _
      simpa only [abs_of_nonneg (log_increment_bounds n).1] using hΦ (Real.log (n+2 : ℕ)) (Real.log (n+1 : ℕ))
    _ = L*Real.log N := by
      rw [← mul_sum]
      have hh := sum_range_sub (fun n : ℕ => Real.log (n+1 : ℕ)) (N-1)
      simp only [Nat.sub_add_cancel (Nat.pos_of_ne_zero hN), Nat.zero_add, Nat.cast_one, Real.log_one, sub_zero] at hh
      rw [hh]

/-- A uniform prefix error can be tested against any such nonlinear weight. -/
theorem logarithmic_weighted_prefix_bound (Φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hΦ : ∀ x y, |Φ x-Φ y| ≤ L*|x-y|) (z : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {E : ℝ} (hE : ∀ j ≤ N, |∑ n ∈ Ioc 0 j, z n| ≤ E) :
    |∑ n ∈ Ioc 0 N, Φ (Real.log n)*z n| ≤
      (|Φ (Real.log N)|+L*Real.log N)*E := by
  have hh := abs_weighted_prefix (fun n => Φ (Real.log (n+1 : ℕ))) (fun n => z (n+1))
    N E (|Φ (Real.log N)|) (L*Real.log N)
    (by intro j hj; rw [← sum_Ioc_zero_eq_sum_range_succ]; exact hE j hj)
    (by dsimp only; rw [Nat.sub_add_cancel hN]) (by simpa only [Nat.add_assoc] using logarithmic_variation_bound Φ hL hΦ N)
  simpa only [sum_Ioc_zero_eq_sum_range_succ] using hh

noncomputable def centeredLogWeight (Φ : ℝ → ℝ) (F : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, Φ (Real.log (n+1 : ℕ))*(F (n+1)-F n-F N/N)

noncomputable def centeredMeanBudget (F : ℕ → ℝ) (c : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, |F (n+1)/(n+1 : ℕ)-c|)+(N : ℝ)*|F N/N-c|

lemma centeredMeanBudget_nonneg (F : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    0 ≤ centeredMeanBudget F c N := by
  unfold centeredMeanBudget
  positivity

/-- Uniform over all weights with the specified Lipschitz constant. The
value of the weight at zero is unrestricted, since constants cancel. -/
theorem centeredLogWeight_bound (Φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hΦ : ∀ x y, |Φ x-Φ y| ≤ L*|x-y|)
    (F : ℕ → ℝ) (hF0 : F 0 = 0) (c : ℝ) (N : ℕ) :
    |centeredLogWeight Φ F N| ≤ L*centeredMeanBudget F c N := by
  by_cases hN : N = 0
  · simp [hN, centeredLogWeight, centeredMeanBudget]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have he := sum_range_by_parts (fun n => Φ (Real.log (n+1 : ℕ)))
    (fun n => F (n+1)-F n-F N/N) N
  simp only [smul_eq_mul, centered_prefix F hF0] at he
  rw [div_mul_cancel₀ (F N) hN0, sub_self, mul_zero, zero_sub] at he
  change centeredLogWeight Φ F N = _ at he
  rw [he, abs_neg]
  have hpoint (n : ℕ) :
      |(Φ (Real.log (n+2 : ℕ))-Φ (Real.log (n+1 : ℕ)))*
        (F (n+1)-(F N/N)*(n+1 : ℕ))| ≤
      L*(|F (n+1)/(n+1 : ℕ)-c|+|F N/N-c|) := by
    have hn : (0 : ℝ) < (n+1 : ℕ) := by positivity
    have hlog := log_increment_bounds n
    have hphi : |Φ (Real.log (n+2 : ℕ))-Φ (Real.log (n+1 : ℕ))| ≤
        L*(Real.log (n+2 : ℕ)-Real.log (n+1 : ℕ)) := by
      simpa only [abs_of_nonneg hlog.1] using hΦ (Real.log (n+2 : ℕ)) (Real.log (n+1 : ℕ))
    have hfactor : |Φ (Real.log (n+2 : ℕ))-Φ (Real.log (n+1 : ℕ))| *(n+1 : ℕ) ≤ L := by
      have hh := mul_le_mul_of_nonneg_right hphi hn.le
      have hk := mul_le_mul_of_nonneg_left hlog.2 hL
      nlinarith only [hh, hk]
    have hid : F (n+1)-(F N/N)*(n+1 : ℕ) =
        (n+1 : ℕ)*(F (n+1)/(n+1 : ℕ)-F N/N) := by field_simp
    rw [hid, abs_mul, abs_mul, abs_of_nonneg hn.le, ← mul_assoc]
    have hdiff : |F (n+1)/(n+1 : ℕ)-F N/N| ≤
        |F (n+1)/(n+1 : ℕ)-c|+|F N/N-c| := by
      simpa only [abs_sub_comm c (F N/N)] using abs_sub_le (F (n+1)/(n+1 : ℕ)) c (F N/N)
    exact (mul_le_mul_of_nonneg_right hfactor (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hdiff hL)
  calc
    _ ≤ ∑ n ∈ range (N-1), |(Φ (Real.log (n+1+1 : ℕ))-Φ (Real.log (n+1 : ℕ)))*
        (F (n+1)-(F N/N)*(n+1 : ℕ))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ range (N-1), L*(|F (n+1)/(n+1 : ℕ)-c|+|F N/N-c|) :=
      sum_le_sum (fun n _ => hpoint n)
    _ ≤ ∑ n ∈ range N, L*(|F (n+1)/(n+1 : ℕ)-c|+|F N/N-c|) :=
      sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le _ _)) (fun _ _ _ => by positivity)
    _ = _ := by simp only [centeredMeanBudget, mul_add, sum_add_distrib, ← mul_sum,
        sum_const, card_range, nsmul_eq_mul]

/-- Only qualitative convergence of the endpoint averages is needed. -/
theorem centeredMeanBudget_div_tendsto (F : ℕ → ℝ) (c : ℝ)
    (hF : Tendsto (fun N : ℕ => F N/N) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ => centeredMeanBudget F c N/N) atTop (𝓝 0) := by
  have hshift := hF.comp (tendsto_add_atTop_nat 1)
  have he : Tendsto (fun n : ℕ => |F (n+1)/(n+1 : ℕ)-c|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hshift.sub_const c).abs
  have hces : Tendsto (fun N : ℕ => (∑ n ∈ range N, |F (n+1)/(n+1 : ℕ)-c|)/N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_comm] using he.cesaro
  have hend : Tendsto (fun N : ℕ => |F N/N-c|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hF.sub_const c).abs
  have hh := hces.add hend
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [centeredMeanBudget, add_div, mul_div_cancel_left₀ _ hNR]

#print axioms logarithmic_weighted_prefix_bound
#print axioms centeredLogWeight_bound
#print axioms centeredMeanBudget_div_tendsto

end Erdos972LipschitzLogWeights
