import Submission.KernelPoleLower

/-! Finite logarithmic prime sums on a quadratic cutoff scale. -/
namespace Erdos972LogPrimeSums

open Finset Complex Filter
open Erdos972ExponentialSum Erdos972LogPrimeBlocks Erdos972PrimeDirichletPole
open Erdos972PrimeRatioKernel Erdos972KernelPoleLower

lemma primeWeight_eq_exp (ε : ℝ) {p : ℕ} (hp : p.Prime) :
    primeWeight ε p = Real.log p * Real.exp (-(1 + ε) * Real.log p) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  rw [show -(1 + ε) * Real.log p = -Real.log p + -ε * Real.log p by ring,
    Real.exp_add, Real.exp_neg, Real.exp_log hpR]
  unfold primeWeight
  ring

lemma prime_term_eq_weight_phase (ε t : ℝ) {p : ℕ} (hp : p.Prime) :
    LSeries.term primeCoeff (((1 + ε : ℝ) : ℂ) + Complex.I * ((-2 * Real.pi * t : ℝ) : ℂ)) p =
      (primeWeight ε p : ℂ) * phase (t * Real.log p) := by
  rw [LSeries.term_of_ne_zero hp.ne_zero, primeCoeff, if_pos hp,
    Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hp.ne_zero), div_eq_mul_inv,
    ← Complex.exp_neg, ← Complex.natCast_log]
  have he : -((Real.log p : ℂ) * (((1 + ε : ℝ) : ℂ) + Complex.I * ((-2 * Real.pi * t : ℝ) : ℂ))) =
      ((-(1 + ε) * Real.log p : ℝ) : ℂ) +
        ((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((t * Real.log p : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, Complex.exp_add, primeWeight_eq_exp ε hp]
  unfold phase
  simp only [Complex.ofReal_mul, Complex.ofReal_exp]
  ring

noncomputable def primeWindow (B L : ℕ) : Finset ℕ := by
  classical
  exact (truncPrimes L).filter fun p => B < p

lemma mem_primeWindow {B L p : ℕ} (hp : p ∈ primeWindow B L) :
    B < p ∧ p.Prime ∧ 0 ≤ Real.log p ∧ Real.log p ≤ L := by
  obtain ⟨hpL, hpB⟩ := mem_filter.mp hp
  have hh := log_le_of_mem_truncPrimes hpL
  exact ⟨hpB, hh.1, Real.log_nonneg (by exact_mod_cast hh.1.one_le), hh.2⟩

lemma primeTrunc_eq_weightedExpSum (ε t : ℝ) (L : ℕ) :
    primeTrunc ε (-2 * Real.pi * t) L =
      weightedExpSum (truncPrimes L) (primeWeight ε) (fun p => Real.log p) t := by
  apply sum_congr rfl
  intro p hp
  exact prime_term_eq_weight_phase ε t (log_le_of_mem_truncPrimes hp).1

lemma norm_window_sub_trunc_le {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) (B L : ℕ) :
    ‖weightedExpSum (primeWindow B L) (primeWeight ε) (fun p => Real.log p) t -
      primeTrunc ε (-2 * Real.pi * t) L‖ ≤ Chebyshev.theta B := by
  classical
  rw [primeTrunc_eq_weightedExpSum]
  let f : ℕ → ℂ := fun p => (primeWeight ε p : ℂ) * phase (t * Real.log p)
  have he := sum_filter_add_sum_filter_not (truncPrimes L) (fun p => B < p) f
  have hd : weightedExpSum (primeWindow B L) (primeWeight ε) (fun p => Real.log p) t -
      weightedExpSum (truncPrimes L) (primeWeight ε) (fun p => Real.log p) t =
        -(∑ p ∈ (truncPrimes L).filter (fun p => ¬B < p), f p) := by
    change (∑ p ∈ (truncPrimes L).filter (fun p => B < p), f p) - (∑ p ∈ truncPrimes L, f p) = _
    rw [← he]
    ring
  rw [hd, norm_neg]
  calc
    _ ≤ ∑ p ∈ (truncPrimes L).filter (fun p => ¬B < p), ‖f p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ (truncPrimes L).filter (fun p => ¬B < p), Real.log p := by
      apply sum_le_sum
      intro p hp
      have hpp := (log_le_of_mem_truncPrimes (mem_filter.mp hp).1).1
      have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_le
      dsimp [f]
      rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (primeWeight_nonneg ε hpp)]
      apply (primeWeight_le_log_div hε hpp).trans
      exact div_le_self (Real.log_nonneg hpR) hpR
    _ ≤ Chebyshev.theta B := by
      rw [Chebyshev.theta, Nat.floor_natCast]
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpL, hpB⟩ := mem_filter.mp hp
        have hpp := (log_le_of_mem_truncPrimes hpL).1
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpp.pos, Nat.le_of_not_gt hpB⟩, hpp⟩
      · intro p hp _
        exact Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le)

lemma inv_one_sub_exp_neg_le {ε : ℝ} (hε : 0 < ε) :
    1 / (1 - Real.exp (-ε)) ≤ 1 + 1 / ε := by
  have h1 : 0 < 1 + ε := by linarith
  have he : 1 + ε ≤ Real.exp ε := by linarith [Real.add_one_le_exp ε]
  have hi := one_div_le_one_div_of_le h1 he
  rw [one_div, ← Real.exp_neg] at hi
  have hlo : ε / (1 + ε) ≤ 1 - Real.exp (-ε) := by
    have hh : ε / (1 + ε) = 1 - 1 / (1 + ε) := by field_simp; ring
    rw [hh]
    simpa only [one_div] using sub_le_sub_left hi 1
  have hpos : 0 < ε / (1 + ε) := div_pos hε h1
  have hh := one_div_le_one_div_of_le hpos hlo
  have heq : 1 / (ε / (1 + ε)) = 1 + 1 / ε := by field_simp; ring
  rwa [heq] at hh

lemma quadratic_tail_le {u : ℕ} (hu : 0 < u) :
    Real.exp 1 * Real.log 4 * Real.exp (-(1 / (u : ℝ)) * (u ^ 2 : ℕ)) /
      (1 - Real.exp (-(1 / (u : ℝ)))) ≤
        (Real.exp 1 * Real.log 4) * (1 + u) * Real.exp (-(u : ℝ)) := by
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have he : -(1 / (u : ℝ)) * (u ^ 2 : ℕ) = -(u : ℝ) := by push_cast; field_simp
  rw [he, div_eq_mul_inv, ← one_div]
  calc
    _ ≤ (Real.exp 1 * Real.log 4 * Real.exp (-(u : ℝ))) * (1 + 1 / (1 / (u : ℝ))) :=
      mul_le_mul_of_nonneg_left (inv_one_sub_exp_neg_le (by positivity)) (by positivity)
    _ = _ := by simp only [one_div_one_div]; ring

lemma eventually_quadratic_tail_le_one :
    ∀ᶠ u : ℕ in atTop,
      Real.exp 1 * Real.log 4 * Real.exp (-(1 / (u : ℝ)) * (u ^ 2 : ℕ)) /
        (1 - Real.exp (-(1 / (u : ℝ)))) ≤ 1 := by
  have h0 := Real.tendsto_exp_neg_atTop_nhds_zero
  have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  simp only [pow_one] at h1
  have hlim : Tendsto (fun x : ℝ => (Real.exp 1 * Real.log 4) * (1 + x) * Real.exp (-x))
      atTop (nhds 0) := by
    convert (h0.add h1).const_mul (Real.exp 1 * Real.log 4) using 1
    · funext x
      ring
    · simp
  have hn := (hlim.comp tendsto_natCast_atTop_atTop).eventually_le_const (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hn, eventually_gt_atTop (0 : ℕ)] with u hsmall hu
  exact (quadratic_tail_le hu).trans hsmall

/-- The truncated prime sum, even after deleting every input up to `B`, has a
uniform bounded pole error at all sufficiently large quadratic cutoff scales. -/
theorem eventually_window_pole_bound (B : ℕ) (T : ℝ) (_hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ u : ℕ in atTop, ∀ t : ℝ, |t| ≤ T →
      ‖weightedExpSum (primeWindow B (u ^ 2)) (primeWeight (1 / u)) (fun p => Real.log p) t -
        pole (1 / u) t‖ ≤ C := by
  obtain ⟨C, hC, hp⟩ := uniform_primeTrunc_pole_bound (2 * Real.pi * T)
  refine ⟨Chebyshev.theta B + C + 1, by have := Chebyshev.theta_nonneg B; positivity, ?_⟩
  filter_upwards [eventually_quadratic_tail_le_one, eventually_ge_atTop (1 : ℕ)] with u hu hu1
  intro t ht
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu1
  have hε : 0 < 1 / (u : ℝ) := by positivity
  have hε1 : 1 / (u : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr huR
  have ht' : |-2 * Real.pi * t| ≤ 2 * Real.pi * T := by
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  have hh := hp (1 / u) (-2 * Real.pi * t) hε hε1 ht' (u ^ 2)
  have hr := norm_window_sub_trunc_le hε.le t B (u ^ 2)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (weightedExpSum (primeWindow B (u ^ 2)) (primeWeight (1 / u)) (fun p => Real.log p) t)
    (primeTrunc (1 / u) (-2 * Real.pi * t) (u ^ 2)) (pole (1 / u) t)
  change ‖primeTrunc (1 / u) (-2 * Real.pi * t) (u ^ 2) - pole (1 / u) t‖ ≤ _ at hh
  linarith

lemma weightedExpSum_zero (S : Finset ℕ) (w x : ℕ → ℝ) :
    weightedExpSum S w x 0 = ((∑ p ∈ S, w p : ℝ) : ℂ) := by
  simp [weightedExpSum, phase]

lemma mass_le_of_pole_zero (S : Finset ℕ) (w x : ℕ → ℝ) {u C : ℝ} (_hu : 0 < u)
    (hC : C ≤ u) (hp : ‖weightedExpSum S w x 0 - pole (1 / u) 0‖ ≤ C) :
    (∑ p ∈ S, w p) ≤ 2 * u := by
  have he : pole (1 / u) 0 = (u : ℂ) := by simp [pole]
  rw [he, weightedExpSum_zero, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hp
  linarith [(abs_le.mp hp).2]

#print axioms eventually_window_pole_bound
#print axioms mass_le_of_pole_zero

end Erdos972LogPrimeSums
