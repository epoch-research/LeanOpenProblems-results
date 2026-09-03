import Submission.DampedDivisorKernel

/-!
A fixed-parameter mean-square tail bound uniform in the input cutoff.
Unlike the earlier divisor-cardinality bound, its constant does not grow
with N. It does not assert that the bound is small in every joint limit
where t tends to zero and N tends to infinity.
-/
namespace Erdos972UniformDampedTail

open Finset Filter ArithmeticFunction
open scoped ArithmeticFunction.Moebius Topology
open Erdos972DampedDivisorKernel Erdos972SmoothMangoldt
open Erdos972SmoothDivisorTail Erdos972ExponentialSum

noncomputable def positiveDivisorSum (t : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, Real.exp (-t*Real.log d)

lemma positiveDivisorSum_nonneg (t : ℝ) (n : ℕ) : 0 ≤ positiveDivisorSum t n :=
  sum_nonneg fun _ _ => (Real.exp_pos _).le

lemma divisor_sum_box {n N : ℕ} (hn : n ∈ Ioc 0 N) (f : ℕ → ℝ) :
    (∑ d ∈ n.divisors, f d) = ∑ d ∈ Ioc 0 N, if d ∣ n then f d else 0 := by
  classical
  rw [← sum_filter]
  congr 1
  ext d
  simp only [Nat.mem_divisors, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨hd, hn0⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd (mem_Ioc.mp hn).1,
      (Nat.le_of_dvd (mem_Ioc.mp hn).1 hd).trans (mem_Ioc.mp hn).2⟩, hd⟩
  · rintro ⟨_, hd⟩
    exact ⟨hd, (mem_Ioc.mp hn).1.ne'⟩

lemma positiveDivisorSum_energy_exact (t : ℝ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (positiveDivisorSum t n)^2) =
      ∑ d ∈ Ioc 0 N, ∑ e ∈ Ioc 0 N,
        (N / Nat.lcm d e : ℕ) *
          (Real.exp (-t*Real.log d)*Real.exp (-t*Real.log e)) := by
  classical
  have hs (n : ℕ) (hn : n ∈ Ioc 0 N) : (positiveDivisorSum t n)^2 =
      ∑ d ∈ Ioc 0 N, ∑ e ∈ Ioc 0 N,
        if d ∣ n ∧ e ∣ n then Real.exp (-t*Real.log d)*Real.exp (-t*Real.log e) else 0 := by
    rw [positiveDivisorSum, divisor_sum_box hn, pow_two, sum_mul_sum]
    apply sum_congr rfl
    intro d _
    apply sum_congr rfl
    intro e _
    split_ifs <;> simp_all
  rw [sum_congr rfl hs, sum_comm]
  apply sum_congr rfl
  intro d _
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  simp_rw [← Nat.lcm_dvd_iff]
  rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]

/-- Uniform in N; the finite constant is a convergent two-variable series. -/
theorem positiveDivisorSum_energy {t : ℝ} (ht : 0 < t) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (positiveDivisorSum t n)^2) ≤ (N : ℝ)*kernelMass t := by
  rw [positiveDivisorSum_energy_exact]
  calc
    _ ≤ ∑ d ∈ Ioc 0 N, ∑ e ∈ Ioc 0 N, (N : ℝ)*kernel t (d,e) := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro e he
      have hd0 := (mem_Ioc.mp hd).1
      have he0 := (mem_Ioc.mp he).1
      rw [kernel_lcm hd0 he0]
      calc
        _ ≤ ((N : ℝ)/(Nat.lcm d e : ℝ)) *
            (Real.exp (-t*Real.log d)*Real.exp (-t*Real.log e)) :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
        _ = _ := by ring
    _ = (N : ℝ)*∑ z ∈ Ioc 0 N ×ˢ Ioc 0 N, kernel t z := by
      rw [sum_product]
      simp only [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_kernel ht).sum_le_tsum _ (fun z _ => kernel_nonneg t z)) (Nat.cast_nonneg N)

lemma abs_expTail_le_positiveDivisorSum {t : ℝ} (ht : 0 ≤ t) (D n : ℕ) :
    |expTail t D n| ≤ damping (t/2) D * positiveDivisorSum (t/2) n := by
  classical
  rw [expTail_eq]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ n.divisors.filter (fun d => D < d),
        damping (t/2) D * Real.exp (-(t/2)*Real.log d) := by
      apply sum_le_sum
      intro d hd
      have hDd := (mem_filter.mp hd).2.le
      have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := d)
      rw [dampedCoefficient, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ Real.exp (-t*Real.log d) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hμ (Real.exp_pos _).le
        _ = Real.exp (-(t/2)*Real.log d)*Real.exp (-(t/2)*Real.log d) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (monotone_log_natCast hDd) (by linarith)))
          (Real.exp_pos _).le
    _ ≤ ∑ d ∈ n.divisors, damping (t/2) D * Real.exp (-(t/2)*Real.log d) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity [damping_pos (t/2) D])
    _ = _ := by rw [positiveDivisorSum, mul_sum]

lemma damping_half_square (t : ℝ) (D : ℕ) : (damping (t/2) D)^2 = damping t D := by
  unfold damping
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- A bound of the form N * D^(-t) * C(t), with finite C(t) for every t>0.
No logarithmic factor depending on N occurs. -/
theorem expTail_uniform_energy {t : ℝ} (ht : 0 < t) (D N : ℕ) :
    (∑ n ∈ Ioc 0 N, (expTail t D n)^2) ≤
      (N : ℝ)*damping t D*kernelMass (t/2) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, (damping (t/2) D * positiveDivisorSum (t/2) n)^2 := by
      apply sum_le_sum
      intro n _
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (abs_expTail_le_positiveDivisorSum ht.le D n) 2
    _ = damping t D * ∑ n ∈ Ioc 0 N, (positiveDivisorSum (t/2) n)^2 := by
      simp only [mul_pow, damping_half_square, mul_sum]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left
        (positiveDivisorSum_energy (show 0 < t/2 by positivity) N) (damping_pos t D).le
      nlinarith only [hh]

lemma damping_tendsto_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (damping t) atTop (𝓝 0) := by
  have hl := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hm := hl.const_mul_atTop ht
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hm
  change Tendsto (fun D : ℕ => Real.exp (-t*Real.log D)) atTop (𝓝 0)
  simpa only [Function.comp_def, ← neg_mul] using he

/-- The divisor tail can be made small in normalized mean square by one
fixed cutoff D, simultaneously for every input cutoff N. -/
theorem exists_uniform_tail_cutoff {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ∃ D : ℕ, ∀ N : ℕ,
      (∑ n ∈ Ioc 0 N, (expTail t D n)^2) ≤ ε*N := by
  have hh := (damping_tendsto_zero ht).mul_const (kernelMass (t/2))
  simp only [zero_mul] at hh
  obtain ⟨D, hD⟩ := ((tendsto_order.mp hh).2 ε hε).exists
  refine ⟨D, fun N => (expTail_uniform_energy ht D N).trans ?_⟩
  have h := mul_le_mul_of_nonneg_left hD.le (Nat.cast_nonneg N)
  nlinarith only [h]

#print axioms positiveDivisorSum_energy
#print axioms expTail_uniform_energy
#print axioms exists_uniform_tail_cutoff

end Erdos972UniformDampedTail
