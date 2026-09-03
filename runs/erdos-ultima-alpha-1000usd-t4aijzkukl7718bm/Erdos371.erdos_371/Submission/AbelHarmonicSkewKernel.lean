import FormalConjecturesUtil

/-! Finite positive-shift averaging kernels whose imaginary Fourier multipliers
are uniformly small. These kernels average over auxiliary integer shifts, not
just primes; no arithmetic comparison cancellation is asserted here. -/
namespace Erdos371.SkewKernel
open Finset Filter
open scoped Topology

noncomputable def harmonicPolynomial (H : ℕ) (r : ℝ) (z : ℂ) : ℂ :=
  ∑ k ∈ range H, (r : ℂ)^k * z^k / k

noncomputable def harmonicMass (H : ℕ) (r : ℝ) : ℝ :=
  ∑ k ∈ range H, r^k / k

lemma harmonicPolynomial_one (H : ℕ) (r : ℝ) :
    harmonicPolynomial H r 1 = (harmonicMass H r : ℂ) := by
  simp [harmonicPolynomial, harmonicMass]

lemma harmonicPolynomial_eq_neg_logTaylor (H : ℕ) (r : ℝ) (z : ℂ) :
    harmonicPolynomial H r z = -Complex.logTaylor H (-((r : ℂ)*z)) := by
  unfold harmonicPolynomial Complex.logTaylor
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro k _
  rw [show (-((r : ℂ)*z))^k = (-1)^k*((r : ℂ)*z)^k by exact neg_pow _ _,
    pow_succ (-1 : ℂ), mul_pow]
  have he : (-1 : ℂ)^k * (-1)^k = 1 := by rw [← mul_pow]; norm_num
  linear_combination (-(r : ℂ)^k*z^k/(k : ℂ)) * he

lemma harmonicPolynomial_log_error (H : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖harmonicPolynomial (H+1) r z - (-Complex.log (1-(r : ℂ)*z))‖ ≤
      r^(H+1) / (1-r) := by
  have hnorm : ‖(r : ℂ)*z‖ ≤ r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    nlinarith [norm_nonneg z]
  have hd : 0 < 1-r := sub_pos.mpr hr1
  have hdn : 0 < 1-‖(r : ℂ)*z‖ := sub_pos.mpr (hnorm.trans_lt hr1)
  have hsmall : ‖-((r : ℂ)*z)‖ < 1 := by simpa using hnorm.trans_lt hr1
  have hb := Complex.norm_log_sub_logTaylor_le H hsmall
  rw [harmonicPolynomial_eq_neg_logTaylor]
  have he : -Complex.logTaylor (H+1) (-((r : ℂ)*z)) -
      -Complex.log (1-(r : ℂ)*z) =
      Complex.log (1+-((r : ℂ)*z)) - Complex.logTaylor (H+1) (-((r : ℂ)*z)) := by
    rw [← sub_eq_add_neg]
    ring
  rw [he]
  apply hb.trans
  simp only [norm_neg]
  calc
    _ ≤ ‖(r : ℂ)*z‖^(H+1) * (1-‖(r : ℂ)*z‖)⁻¹ := by
      apply div_le_self (by positivity)
      norm_num
    _ ≤ r^(H+1) * (1-r)⁻¹ := by
      gcongr
    _ = _ := by rw [div_eq_mul_inv]

lemma neg_log_im_abs_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (z : ℂ) (hz : ‖z‖ ≤ 1) : |(-Complex.log (1-(r : ℂ)*z)).im| ≤ Real.pi/2 := by
  simp only [Complex.neg_im, abs_neg, Complex.log_im]
  apply Complex.abs_arg_le_pi_div_two_iff.mpr
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have hzre : z.re ≤ 1 := (le_abs_self _).trans ((Complex.abs_re_le_norm z).trans hz)
  nlinarith

lemma harmonicPolynomial_im_bound (H : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    |(harmonicPolynomial (H+1) r z).im| ≤ Real.pi/2+r^(H+1)/(1-r) := by
  have he := (Complex.abs_im_le_norm
    (harmonicPolynomial (H+1) r z - (-Complex.log (1-(r : ℂ)*z)))).trans
      (harmonicPolynomial_log_error H hr hr1 z hz)
  have hl := neg_log_im_abs_le hr hr1 z hz
  have ht := abs_sub_le (harmonicPolynomial (H+1) r z).im
    (-Complex.log (1-(r : ℂ)*z)).im 0
  simp only [Complex.sub_im] at he
  simp only [sub_zero] at ht
  linarith

lemma harmonicMass_tendsto {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun H => harmonicMass H r) atTop (nhds (-Real.log (1-r))) := by
  have hc : ‖(r : ℂ)‖ < 1 := by simpa [abs_of_nonneg hr] using hr1
  have hs := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hc)
  have ht := hs.tendsto_sum_nat
  convert ht using 1
  · ext H
    simp [harmonicMass, ← Complex.ofReal_pow, ← Complex.ofReal_natCast,
      ← Complex.ofReal_div]
  · rw [Complex.neg_re, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.log_ofReal_re]

/-- A finite probability distribution on strictly positive integer shifts can
make its imaginary polynomial uniformly small on the closed unit disk.
There is no restriction of the supporting shifts to primes. -/
theorem exists_positive_shift_kernel (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, ∃ w : ℕ → ℝ,
      (∀ k, 0 ≤ w k) ∧ w 0 = 0 ∧ (∀ k, H ≤ k → w k = 0) ∧
      (∑ k ∈ range H, w k) = 1 ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → |(∑ k ∈ range H, (w k : ℂ)*z^k).im| < ε := by
  let M : ℝ := 4*(Real.pi/2+1)/ε
  have hM : 0 < M := by dsimp [M]; positivity
  let r : ℝ := 1-Real.exp (-M)
  have hr : 0 < r := by
    dsimp [r]
    have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hM)
    linarith
  have hr1 : r < 1 := by dsimp [r]; linarith [Real.exp_pos (-M)]
  have hmass : -Real.log (1-r) = M := by simp [r, Real.log_exp]
  have ht := harmonicMass_tendsto hr.le hr1
  rw [hmass] at ht
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1).div_const (1-r)
  have hev : ∀ᶠ H : ℕ in atTop,
      M/2 < harmonicMass (H+1) r ∧ r^(H+1)/(1-r) < 1 := by
    have hshift : Tendsto (fun H : ℕ => H+1) atTop atTop := tendsto_add_atTop_nat 1
    have hm := (ht.comp hshift).eventually_const_lt (by linarith : M/2 < M)
    have hp := (hpow.comp hshift).eventually_lt_const (by norm_num : (0 : ℝ)/(1-r) < 1)
    exact hm.and hp
  obtain ⟨H,hm,hp⟩ := hev.exists
  let S := harmonicMass (H+1) r
  have hS : 0 < S := by dsimp [S]; linarith
  let w : ℕ → ℝ := fun k => if k < H+1 then (r^k/k)/S else 0
  refine ⟨H+1,w,?_,?_,?_,?_,?_⟩
  · intro k
    dsimp [w]
    split_ifs <;> positivity
  · simp [w]
  · intro k hk
    dsimp [w]
    rw [if_neg (not_lt.mpr hk)]
  · have he : (∑ k ∈ range (H+1), w k) = S/S := by
      change (∑ k ∈ range (H+1), if k < H+1 then (r^k/k)/S else 0) = _
      calc
        _ = (∑ k ∈ range (H+1), (r^k/k)/S) := by
          apply sum_congr rfl
          intro k hk
          rw [if_pos (mem_range.mp hk)]
        _ = S/S := by rw [← sum_div]; rfl
    rw [he, div_self hS.ne']
  · intro z hz
    have he : (∑ k ∈ range (H+1), (w k : ℂ)*z^k) =
        harmonicPolynomial (H+1) r z / (S : ℂ) := by
      unfold harmonicPolynomial
      rw [sum_div]
      apply sum_congr rfl
      intro k hk
      dsimp [w]
      rw [if_pos (mem_range.mp hk)]
      push_cast
      ring
    rw [he, Complex.div_ofReal_im, abs_div, abs_of_pos hS]
    apply (div_lt_iff₀ hS).mpr
    have hb := harmonicPolynomial_im_bound H hr.le hr1 z hz
    have hMS : M/2 < S := hm
    have hprod := mul_lt_mul_of_pos_left hMS hε
    have hMe : ε*(M/2) = 2*(Real.pi/2+1) := by dsimp [M]; field_simp; ring
    rw [hMe] at hprod
    nlinarith [Real.pi_pos]

#print axioms exists_positive_shift_kernel
end Erdos371.SkewKernel
