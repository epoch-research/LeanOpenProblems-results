import Submission.LocalWideBadSlopes
import Submission.RationalRoute

/-! Rational exclusions remove less than half of the one-sided hole at
arbitrarily large metric scales for each prescribed irrational slope. -/
namespace Erdos972LocalRationalHoleScales

open Set MeasureTheory Filter
open scoped Topology
open Erdos972LocalWideBadSlopes Erdos972WideMetricSieve

lemma denominator_scale (q : ℕ) (hq : 0 < q) :
    ∃ v : ℕ, 0 < v ∧ v^26 ≤ q ∧ q < 2^26 * v^26 := by
  let k := Nat.log (2^26) q
  refine ⟨2^k, by positivity, ?_, ?_⟩
  · have hh := Nat.pow_log_le_self (2^26) (Nat.ne_of_gt hq)
    simpa only [k, ← pow_mul, Nat.mul_comm 26] using hh
  · have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)^26) q
    change q < (2^26)^(k+1) at hh
    have he : (2^26)^(k+1) = 2^26 * (2^k)^26 := by
      calc
        _ = 2^26 * (2^26)^k := pow_succ' _ _
        _ = _ := by
          congr 1
          rw [← pow_mul, ← pow_mul, Nat.mul_comm 26 k]
    rwa [he] at hh

lemma approximation_budget {x q C : ℝ} (hx : 0 < x) (hql : x^26 ≤ q)
    (hqu : q ≤ C * x^26) :
    ((1 / q^2 + 1 / (2 * x^40)) * x^13 + 1 / x^28) * q ≤
      1 / x^13 + C / (2 * x) + C / x^2 := by
  have hq : 0 < q := (pow_pos hx _).trans_le hql
  have h₁ : x^13 / q ≤ 1 / x^13 := by
    apply (div_le_div_iff₀ hq (pow_pos hx _)).mpr
    nlinarith only [hql, show x^13 * x^13 = x^26 by ring]
  have h₂ : q * x^13 / (2 * x^40) ≤ C / (2 * x) := by
    calc
      _ ≤ (C * x^26) * x^13 / (2 * x^40) := by gcongr
      _ = _ := by field_simp
  have h₃ : q / x^28 ≤ C / x^2 := by
    calc
      _ ≤ (C * x^26) / x^28 := div_le_div_of_nonneg_right hqu (by positivity)
      _ = _ := by field_simp
  have he : ((1 / q^2 + 1 / (2 * x^40)) * x^13 + 1 / x^28) * q =
      x^13 / q + q * x^13 / (2 * x^40) + q / x^28 := by field_simp
  rw [he]
  linarith

lemma approximation_budget_tendsto (C : ℝ) :
    Tendsto (fun v : ℕ => 1 / (v : ℝ)^13 + C / (2 * (v : ℝ)) + C / (v : ℝ)^2)
      atTop (𝓝 0) := by
  have h₁ : Tendsto (fun v : ℕ => 1 / (v : ℝ)^13) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
        (tendsto_id.atTop_pow (by norm_num : 0 < (13:ℕ)))
  have h₂ : Tendsto (fun v : ℕ => C / (2 * (v : ℝ))) atTop (𝓝 0) := by
    simpa only [div_div] using tendsto_const_div_atTop_nhds_zero_nat (C / 2)
  have h₃ : Tendsto (fun v : ℕ => C / (v : ℝ)^2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using
      (tendsto_const_div_atTop_nhds_zero_nat C).comp
        (tendsto_id.atTop_pow (by norm_num : 0 < (2:ℕ)))
  simpa using (h₁.add h₂).add h₃

lemma measure_budget_tendsto :
    Tendsto (fun v : ℕ => 1 / (v : ℝ)^4 + 4 / (v : ℝ)^5 + 2 / (v : ℝ))
      atTop (𝓝 0) := by
  have h₁ : Tendsto (fun v : ℕ => 1 / (v : ℝ)^4) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
        (tendsto_id.atTop_pow (by norm_num : 0 < (4:ℕ)))
  have h₂ : Tendsto (fun v : ℕ => 4 / (v : ℝ)^5) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using
      (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ)).comp
        (tendsto_id.atTop_pow (by norm_num : 0 < (5:ℕ)))
  simpa using (h₁.add h₂).add (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))

lemma local_hole_bound {α : ℝ} (r : ℚ) (A : ℕ) {v : ℕ} (hv : 2 ≤ v)
    (hql : v^26 ≤ r.den) (hqu : r.den ≤ 2^26 * v^26)
    (happrox : |α - r| ≤ 1 / (r.den : ℝ)^2)
    (hsmall : 1 / (v : ℝ)^13 + (2:ℝ)^26 / (2 * (v : ℝ)) + (2:ℝ)^26 / (v : ℝ)^2 < 1) :
    volume.real (Ioo (α - 1 / (2 * (v : ℝ)^40)) α ∩
      wideBadSlopes A (v^24) (v^28)) ≤
      (1 / (v : ℝ)^4 + 4 / (v : ℝ)^5 + 2 / (v : ℝ)) / (v : ℝ)^40 := by
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  have hv1 : (1 : ℝ) < v := by exact_mod_cast (show 1 < v by omega)
  have hq0 : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hqlR : (v : ℝ)^26 ≤ r.den := by exact_mod_cast hql
  have hquR : (r.den : ℝ) ≤ (2:ℝ)^26 * (v : ℝ)^26 := by exact_mod_cast hqu
  have hD : (v : ℝ)^13 < r.den :=
    (pow_lt_pow_right₀ hv1 (by norm_num : (13:ℕ) < 26)).trans_le hqlR
  have hb := (approximation_budget hv0 hqlR hquR).trans_lt hsmall
  have hsmall' : (1 / (r.den : ℝ)^2 + 1 / (2 * (v : ℝ)^40)) * (v : ℝ)^13 +
      1 / (v : ℝ)^28 < 1 / (r.den : ℝ) := (lt_div_iff₀ hq0).mpr hb
  have hm := local_wideBadSlopes_measure (α := α) (ε := 1 / (r.den : ℝ)^2)
    (h := 1 / (2 * (v : ℝ)^40)) (D := (v : ℝ)^13) r A (v^24) (v^28)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    happrox hD (by simpa only [Nat.cast_pow] using hsmall')
  push_cast at hm
  convert hm using 1 <;> field_simp

/-- At arbitrarily large scales the actual rational exceptional sets remove
at most half of the one-sided interval of length `1/(2N)`, with `N=v^40`.
No prime-pair upper or lower estimate is a hypothesis of this theorem. -/
theorem exists_half_hole_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (A B : ℕ) : ∃ v : ℕ, B < v ∧ 2 ≤ v ∧
      volume.real (Ioo (α - 1 / (2 * ((v^40 : ℕ) : ℝ))) α ∩
        wideBadSlopes A (v^24) (v^28)) ≤ 1 / (4 * ((v^40 : ℕ) : ℝ)) := by
  have he₁ := (tendsto_order.mp (approximation_budget_tendsto ((2:ℝ)^26))).2 1 (by norm_num)
  have he₂ := (tendsto_order.mp measure_budget_tendsto).2 (1/4) (by norm_num)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (he₁.and he₂)
  let K := max B (max T 2)
  obtain ⟨r, hr, hqr⟩ := Erdos972RationalRoute.exists_good_approximant_large_den hα hI
    (2^26 * K^26)
  obtain ⟨v, hv0, hvq, hqv⟩ := denominator_scale r.den r.pos
  have hKv : K < v := by
    by_contra hn
    have hpow := Nat.pow_le_pow_left (Nat.le_of_not_gt hn) 26
    have hh := Nat.mul_le_mul_left (2^26) hpow
    omega
  have hBv : B < v := (le_max_left _ _).trans_lt hKv
  have hTv : T ≤ v := ((le_max_left T 2).trans (le_max_right B _)).trans hKv.le
  have hv : 2 ≤ v := ((le_max_right T 2).trans (le_max_right B _)).trans hKv.le
  obtain ⟨he₁v, he₂v⟩ := hT v hTv
  have hm := local_hole_bound r A hv hvq hqv.le hr.le he₁v
  have hvR : (0 : ℝ) < v := Nat.cast_pos.mpr hv0
  have hh := div_le_div_of_nonneg_right he₂v.le (show 0 ≤ (v : ℝ)^40 by positivity)
  refine ⟨v, hBv, hv, ?_⟩
  push_cast
  have he : (1 / 4 : ℝ) / (v : ℝ)^40 = 1 / (4 * (v : ℝ)^40) := by ring
  rw [he] at hh
  exact hm.trans hh

#print axioms local_hole_bound
#print axioms exists_half_hole_scale
end Erdos972LocalRationalHoleScales
