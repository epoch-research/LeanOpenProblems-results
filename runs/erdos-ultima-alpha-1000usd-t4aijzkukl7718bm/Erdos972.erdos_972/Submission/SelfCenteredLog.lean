import Submission.ExponentialSum

/-! Partial summation centered at the actual endpoint average. Qualitative
convergence of the average suffices; no logarithmic rate is required. -/
namespace Erdos972SelfCenteredLog

open Finset Filter
open scoped Topology
open Erdos972ExponentialSum

noncomputable def logIncrement (F : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, Real.log (n+1 : ℕ)*(F (n+1)-F n)

noncomputable def logRow (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, Real.log n*a n

noncomputable def selfCenteredLog (F : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, Real.log (n+1 : ℕ)*(F (n+1)-F n-F N/N)

lemma centered_prefix (F : ℕ → ℝ) (hF0 : F 0 = 0) (ρ : ℝ) (j : ℕ) :
    (∑ n ∈ range j, (F (n+1)-F n-ρ)) = F j-ρ*j := by
  rw [sum_sub_distrib, sum_range_sub, hF0, sub_zero, sum_const, card_range, nsmul_eq_mul]
  ring

lemma selfCenteredLog_by_parts (F : ℕ → ℝ) (hF0 : F 0 = 0) {N : ℕ} (hN : 0 < N) :
    selfCenteredLog F N = -(∑ n ∈ range (N-1),
      (Real.log (n+2 : ℕ)-Real.log (n+1 : ℕ))*(F (n+1)-(F N/N)*(n+1 : ℕ))) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hh := sum_range_by_parts (fun n => Real.log (n+1 : ℕ))
    (fun n => F (n+1)-F n-F N/N) N
  simp only [smul_eq_mul, centered_prefix F hF0] at hh
  rw [div_mul_cancel₀ (F N) hN0, sub_self, mul_zero, zero_sub] at hh
  exact hh

lemma log_increment_bounds (n : ℕ) :
    0 ≤ Real.log (n+2 : ℕ)-Real.log (n+1 : ℕ) ∧
    (Real.log (n+2 : ℕ)-Real.log (n+1 : ℕ))*(n+1 : ℕ) ≤ 1 := by
  have hn : (0 : ℝ) < (n+1 : ℕ) := Nat.cast_pos.mpr (by omega)
  have hn2 : (0 : ℝ) < (n+2 : ℕ) := Nat.cast_pos.mpr (by omega)
  refine ⟨sub_nonneg.mpr (monotone_log_natCast (by omega)), ?_⟩
  have hh := Real.log_le_sub_one_of_pos (div_pos hn2 hn)
  rw [Real.log_div hn2.ne' hn.ne'] at hh
  have hm := mul_le_mul_of_nonneg_right hh hn.le
  have he : (((n+2 : ℕ) : ℝ)/(n+1 : ℕ)-1)*(n+1 : ℕ) = 1 := by
    field_simp
    push_cast
    ring
  rwa [he] at hm

lemma selfCenteredLog_bound (F : ℕ → ℝ) (hF0 : F 0 = 0) (N : ℕ) :
    |selfCenteredLog F N| ≤
      (∑ n ∈ range N, |F (n+1)/(n+1 : ℕ)-1|) + (N : ℝ)*|F N/N-1| := by
  by_cases hN : N = 0
  · simp [hN, selfCenteredLog]
  have hN' : 0 < N := Nat.pos_of_ne_zero hN
  rw [selfCenteredLog_by_parts F hF0 hN', abs_neg]
  have hp (n : ℕ) :
      |(Real.log (n+2 : ℕ)-Real.log (n+1 : ℕ))*(F (n+1)-(F N/N)*(n+1 : ℕ))| ≤
        |F (n+1)/(n+1 : ℕ)-1| + |F N/N-1| := by
    obtain ⟨hlog0, hlog⟩ := log_increment_bounds n
    have hn : (0 : ℝ) < (n+1 : ℕ) := Nat.cast_pos.mpr (by omega)
    have he : F (n+1)-(F N/N)*(n+1 : ℕ) =
        (n+1 : ℕ)*(F (n+1)/(n+1 : ℕ)-F N/N) := by field_simp
    rw [he, abs_mul, abs_mul, abs_of_nonneg hlog0, abs_of_nonneg hn.le, ← mul_assoc]
    calc
      _ ≤ |F (n+1)/(n+1 : ℕ)-F N/N| := by
        simpa using mul_le_mul_of_nonneg_right hlog (abs_nonneg (F (n+1)/(n+1 : ℕ)-F N/N))
      _ ≤ _ := by simpa only [abs_sub_comm 1 (F N/N)] using
        abs_sub_le (F (n+1)/(n+1 : ℕ)) 1 (F N/N)
  calc
    _ ≤ ∑ n ∈ range (N-1), |(Real.log (n+2 : ℕ)-Real.log (n+1 : ℕ))*(F (n+1)-(F N/N)*(n+1 : ℕ))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ range (N-1), (|F (n+1)/(n+1 : ℕ)-1| + |F N/N-1|) := sum_le_sum (fun n _ => hp n)
    _ ≤ ∑ n ∈ range N, (|F (n+1)/(n+1 : ℕ)-1| + |F N/N-1|) :=
      sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le N 1)) (fun _ _ _ => by positivity)
    _ = _ := by rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]

/-- Qualitative asymptotic linearity of `F` makes the endpoint-centered
logarithmic increment sum sublinear. -/
theorem selfCenteredLog_div_tendsto (F : ℕ → ℝ) (hF0 : F 0 = 0)
    (hF : Tendsto (fun N : ℕ => F N/N) atTop (𝓝 1)) :
    Tendsto (fun N : ℕ => selfCenteredLog F N/N) atTop (𝓝 0) := by
  have hshift := hF.comp (tendsto_add_atTop_nat 1)
  have he : Tendsto (fun n : ℕ => |F (n+1)/(n+1 : ℕ)-1|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hshift.sub_const 1).abs
  have hces : Tendsto (fun N : ℕ => (∑ n ∈ range N, |F (n+1)/(n+1 : ℕ)-1|)/N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_comm] using he.cesaro
  have heN : Tendsto (fun N : ℕ => |F N/N-1|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hF.sub_const 1).abs
  apply squeeze_zero_norm' _ (by simpa only [add_zero] using hces.add heN)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hN0.le]
  have hh := div_le_div_of_nonneg_right (selfCenteredLog_bound F hF0 N) hN0.le
  simpa only [add_div, mul_div_cancel_left₀ _ hN0.ne'] using hh

/-- A uniform prefix approximation is preserved under logarithmic weighting
at the usual partial-summation cost. -/
lemma logRow_prefix_approx (a F : ℕ → ℝ) (hF0 : F 0 = 0) (N : ℕ) (E : ℝ)
    (hE : ∀ j ≤ N, |(∑ n ∈ Ioc 0 j, a n)-F j| ≤ E) :
    |logRow a N-logIncrement F N| ≤ 2*Real.log N*E := by
  have hE0 : 0 ≤ E := by simpa [hF0] using hE 0 (Nat.zero_le N)
  by_cases hN : N = 0
  · simp [hN, logRow, logIncrement]
  let z := fun n => a (n+1)-(F (n+1)-F n)
  have hp (j : ℕ) : (∑ n ∈ range j, z n) = (∑ n ∈ Ioc 0 j, a n)-F j := by
    dsimp only [z]
    rw [sum_sub_distrib, sum_range_sub, hF0, sub_zero, sum_Ioc_zero_eq_sum_range_succ]
  have hb : ∀ j ≤ N, ‖∑ n ∈ range j, z n‖ ≤ E := by
    intro j hj
    rw [hp, Real.norm_eq_abs]
    exact hE j hj
  have hh := norm_monotone_weighted_prefix (fun n => Real.log (n+1 : ℕ))
    (fun m n hmn => monotone_log_natCast (Nat.add_le_add_right hmn 1)) (by simp)
    z N E hb
  dsimp only at hh
  rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hN)] at hh
  have he : logRow a N-logIncrement F N = ∑ n ∈ range N, Real.log (n+1 : ℕ) • z n := by
    simp only [logRow, logIncrement, sum_Ioc_zero_eq_sum_range_succ, smul_eq_mul, z,
      mul_sub, sum_sub_distrib]
  simpa only [he, Real.norm_eq_abs] using hh

noncomputable def centeredLogRow (a : ℕ → ℝ) (ρ : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, Real.log n*(a n-ρ)

lemma centeredLogRow_decomposition (a F : ℕ → ℝ) (ρ : ℝ) (N : ℕ) :
    centeredLogRow a ρ N = logRow a N-logIncrement F N+selfCenteredLog F N +
      (F N/N-ρ)*(∑ n ∈ Ioc 0 N, Real.log n) := by
  simp only [centeredLogRow, logRow, logIncrement, selfCenteredLog,
    sum_Ioc_zero_eq_sum_range_succ, mul_sub, sum_sub_distrib, ← sum_mul]
  ring

lemma log_weight_mass_bounds (N : ℕ) :
    0 ≤ (∑ n ∈ Ioc 0 N, Real.log n) ∧ (∑ n ∈ Ioc 0 N, Real.log n) ≤ N*Real.log N := by
  refine ⟨sum_nonneg (fun n _ => Real.log_natCast_nonneg n), ?_⟩
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, Real.log N := sum_le_sum (fun n hn => monotone_log_natCast (mem_Ioc.mp hn).2)
    _ = _ := by simp

/-- The three sources of error after centering: the prefix approximation,
the qualitative self-centered term, and the endpoint mismatch. -/
lemma centeredLogRow_bound (a F : ℕ → ℝ) (hF0 : F 0 = 0) (ρ : ℝ) (N : ℕ) (E : ℝ)
    (hE : ∀ j ≤ N, |(∑ n ∈ Ioc 0 j, a n)-F j| ≤ E) :
    |centeredLogRow a ρ N| ≤ 2*Real.log N*E+|selfCenteredLog F N|+
      Real.log N*|F N-ρ*N| := by
  by_cases hN : N = 0
  · simp [hN, centeredLogRow, selfCenteredLog]
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hb := logRow_prefix_approx a F hF0 N E hE
  have hm := log_weight_mass_bounds N
  have hend : |(F N/N-ρ)*(∑ n ∈ Ioc 0 N, Real.log n)| ≤ Real.log N*|F N-ρ*N| := by
    have he : F N/N-ρ = (F N-ρ*N)/N := by field_simp
    rw [he, abs_mul, abs_div, abs_of_nonneg hN0.le, abs_of_nonneg hm.1]
    calc
      _ ≤ (|F N-ρ*N|/N)*(N*Real.log N) := by gcongr; exact hm.2
      _ = _ := by field_simp
  rw [centeredLogRow_decomposition a F ρ N]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hb le_rfl)) hend)

#print axioms centeredLogRow_bound

#print axioms selfCenteredLog_div_tendsto
#print axioms logRow_prefix_approx

end Erdos972SelfCenteredLog
