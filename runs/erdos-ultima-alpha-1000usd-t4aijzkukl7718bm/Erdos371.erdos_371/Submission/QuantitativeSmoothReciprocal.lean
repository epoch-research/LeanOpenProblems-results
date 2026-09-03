import Submission.RankinSmoothBound
import Submission.PrimeWinnerHarmonicLimits

/-! A logarithmic bound on the total reciprocal mass of smooth integers,
and hence on the total harmonic defect of a largest-prime-factor label
under multiplication. These estimates do not assert natural density. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma nat_neg_rpow_tsum_condensed_bound (s : ℝ) (hs : 1 < s) :
    (∑' n : ℕ, (n : ℝ)^(-s)) ≤ (1-(2 : ℝ)^(1-s))⁻¹ := by
  have hsum := Real.summable_nat_rpow.mpr (show -s < -1 by linarith)
  have hgeo := hasSum_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1-s))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (by linarith : 1-s<0))
  apply le_of_tendsto_of_tendsto
    (hsum.hasSum.tendsto_sum_nat.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ)<2)))
    hgeo.tendsto_sum_nat
  apply Eventually.of_forall
  intro K
  have h := Finset.le_sum_condensed (f := fun n : ℕ => (n : ℝ)^(-s))
    (fun m n hm hmn => Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast hm) (by exact_mod_cast hmn) (by linarith)) K
  have hterm (k : ℕ) : (2^k : ℕ) • (((2^k : ℕ) : ℝ)^(-s)) =
      ((2 : ℝ)^(1-s))^k := by
    simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ)≤2),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ)≤2)]
    rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
    congr 1
    ring
  simpa only [Nat.cast_zero, Real.zero_rpow (show -s≠0 by linarith), zero_add,
    hterm] using h

lemma reciprocal_one_sub_exp_neg_le (x : ℝ) (hx : 0 < x) :
    (1-Real.exp (-x))⁻¹ ≤ 1+1/x := by
  have he : Real.exp (-x) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (show -x < 0 by linarith)
  have hpos : 0 < 1-Real.exp (-x) := by linarith
  have hexp := Real.add_one_le_exp x
  have hprod : (1+x)*Real.exp (-x) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg (-x))
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
    linarith
  apply (inv_le_iff_one_le_mul₀ hpos).mpr
  apply (le_of_mul_le_mul_right ?_ hx)
  calc
    1*x = x := one_mul x
    _ ≤ (1+1/x)*(1-Real.exp (-x))*x := by
      have hid : (1+1/x)*(1-Real.exp (-x))*x =
          1+x-(1+x)*Real.exp (-x) := by field_simp; ring
      rw [hid]
      linarith

lemma primeEulerFactor_comparison (p : ℕ) (hp : p.Prime) (d : ℝ) (hd : 0<d) :
    (1-(p : ℝ)⁻¹)⁻¹ ≤ Real.exp (d*Real.log p/((p : ℝ)-1)) *
      (1-(p : ℝ)^(-(1+d)))⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hA : 0 < 1-(p : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)
  have hB : 0 < 1-(p : ℝ)^(-(1+d)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith))
  have hpow : (p : ℝ)^(-(1+d)) = (p : ℝ)⁻¹*Real.exp (-(d*Real.log p)) := by
    rw [Real.rpow_def_of_pos hp0, show Real.log (p : ℝ)*(-(1+d)) =
      -Real.log p + -(d*Real.log p) by ring, Real.exp_add, Real.exp_neg, Real.exp_log hp0]
  have he := Real.one_sub_le_exp_neg (d*Real.log p)
  have hratio : (1-(p : ℝ)^(-(1+d)))/(1-(p : ℝ)⁻¹) ≤
      1+d*Real.log p/((p : ℝ)-1) := by
    rw [hpow]
    have hid : (1-(p : ℝ)⁻¹*Real.exp (-(d*Real.log p)))/(1-(p : ℝ)⁻¹) =
        1+(1-Real.exp (-(d*Real.log p)))/((p : ℝ)-1) := by
      field_simp [hp0.ne', (sub_pos.mpr hp1).ne']
      ring
    rw [hid]
    apply add_le_add_right
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hexp : 1+d*Real.log p/((p : ℝ)-1) ≤
      Real.exp (d*Real.log p/((p : ℝ)-1)) := by
    simpa only [add_comm] using Real.add_one_le_exp (d*Real.log p/((p : ℝ)-1))
  have hrat := hratio.trans hexp
  have hr := (div_le_iff₀ hA).mp hrat
  apply (le_mul_inv_iff₀ hB).mpr
  apply (inv_mul_le_iff₀ hA).mpr
  nlinarith

lemma primeEulerProduct_rpow_le_tsum (B : ℕ) (s : ℝ) (hs : 1<s) :
    (∏ p ∈ B.primesBelow, (1-(p : ℝ)^(-s))⁻¹) ≤
      ∑' n : ℕ, (n : ℝ)^(-s) := by
  have hp : ∀ {p : ℕ}, p.Prime → ‖natNegRpowHom s p‖<1 := by
    intro p hp
    change ‖(p : ℝ)^(-s)‖<1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have he := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hp B).2
  change HasSum (fun n : B.smoothNumbers => (n.val : ℝ)^(-s))
    (∏ p ∈ B.primesBelow, (1-(p : ℝ)^(-s))⁻¹) at he
  rw [← he.tsum_eq]
  exact Summable.tsum_subtype_le (fun n : ℕ => (n : ℝ)^(-s)) B.smoothNumbers
    (fun _ => by positivity) (Real.summable_nat_rpow.mpr (by linarith))

/-- A coarse upper Mertens product estimate, obtained without the PNT. -/
theorem primeEulerProduct_le_log (B : ℕ) (hB : 1<B) :
    (∏ p ∈ B.primesBelow, (1-(p : ℝ)⁻¹)⁻¹) ≤
      Real.exp 4 * (1+Real.log B/Real.log 2) := by
  have hlog : 0<Real.log B := Real.log_pos (by exact_mod_cast hB)
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let d : ℝ := (Real.log B)⁻¹
  have hd : 0<d := inv_pos.mpr hlog
  have hsum : (∑ p ∈ B.primesBelow, d*Real.log p/((p : ℝ)-1)) ≤ 4 := by
    calc
      _ = d*(∑ p ∈ B.primesBelow, Real.log p/((p : ℝ)-1)) := by
        rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ d*(4*Real.log B) := mul_le_mul_of_nonneg_left (prime_log_div_pred_sum_le B) hd.le
      _ = 4 := by dsimp [d]; field_simp
  have hproduct : (∏ p ∈ B.primesBelow, (1-(p : ℝ)⁻¹)⁻¹) ≤
      Real.exp 4 * (∏ p ∈ B.primesBelow, (1-(p : ℝ)^(-(1+d)))⁻¹) := by
    calc
      _ ≤ ∏ p ∈ B.primesBelow,
          Real.exp (d*Real.log p/((p : ℝ)-1)) * (1-(p : ℝ)^(-(1+d)))⁻¹ := by
        apply Finset.prod_le_prod
        · intro p hp
          exact inv_nonneg.mpr (sub_nonneg.mpr (inv_le_one_of_one_le₀
            (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_le)))
        · intro p hp
          exact primeEulerFactor_comparison p (Nat.mem_primesBelow.mp hp).2 d hd
      _ = Real.exp (∑ p ∈ B.primesBelow, d*Real.log p/((p : ℝ)-1)) *
          (∏ p ∈ B.primesBelow, (1-(p : ℝ)^(-(1+d)))⁻¹) := by
        rw [prod_mul_distrib,Real.exp_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsum)
        apply prod_nonneg
        intro p hp
        apply inv_nonneg.mpr
        have := Real.rpow_lt_one_of_one_lt_of_neg
          (show (1 : ℝ)<p by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_lt)
          (show -(1+d)<0 by linarith)
        linarith
  have hgeo : (1-(2 : ℝ)^(1-(1+d)))⁻¹ ≤ 1+Real.log B/Real.log 2 := by
    have hid : (2 : ℝ)^(1-(1+d)) = Real.exp (-(d*Real.log 2)) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      congr 1
      ring
    rw [hid]
    convert reciprocal_one_sub_exp_neg_le (d*Real.log 2) (mul_pos hd hlog2) using 1
    dsimp [d]
    field_simp
  exact hproduct.trans (mul_le_mul_of_nonneg_left
    ((primeEulerProduct_rpow_le_tsum B (1+d) (by linarith)).trans
      ((nat_neg_rpow_tsum_condensed_bound (1+d) (by linarith)).trans hgeo))
    (Real.exp_nonneg 4))

lemma smoothReciprocal_hasSum (B : ℕ) :
    HasSum (smoothReciprocal B)
      (∏ p ∈ (B+1).primesBelow, (1-(p : ℝ)⁻¹)⁻¹) := by
  have hp : ∀ {p : ℕ}, p.Prime → ‖reciprocalNatHom p‖<1 := by
    intro p hp
    change ‖(p : ℝ)⁻¹‖<1
    rw [norm_inv,Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have he := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hp (B+1)).2
  change HasSum (fun n : (B+1).smoothNumbers => (n.val : ℝ)⁻¹)
    (∏ p ∈ (B+1).primesBelow, (1-(p : ℝ)⁻¹)⁻¹) at he
  have hi := (hasSum_subtype_iff_indicator (f := fun n : ℕ => (n : ℝ)⁻¹)).mp he
  convert hi using 1
  funext n
  simp only [smoothReciprocal,Set.indicator,one_div]

theorem smoothReciprocal_tsum_le_log (B : ℕ) (hB : 0<B) :
    (∑' n, smoothReciprocal B n) ≤
      Real.exp 4 * (1+Real.log (B+1 : ℝ)/Real.log 2) := by
  rw [(smoothReciprocal_hasSum B).tsum_eq]
  simpa only [Nat.cast_add,Nat.cast_one] using primeEulerProduct_le_log (B+1) (by omega)

/-- A pointwise smooth-set majorant uniform in the relabelling. -/
lemma maxPrimeFac_label_harmonic_defect_le {A : Type*} (g : ℕ → A)
    (k n : ℕ) (hk : 0<k) :
    ‖FiniteInformation.labelDilationDefect k (g ∘ Nat.maxPrimeFac) n/(n : ℝ)‖ ≤
      smoothReciprocal k n := by
  classical
  by_cases hn : n=0
  · subst n
    simpa only [Nat.cast_zero,div_zero,norm_zero] using smoothReciprocal_nonneg k 0
  by_cases hp : Nat.maxPrimeFac n ≤ k
  · rw [smoothReciprocal_of_maxPrimeFac_le k n hn hp,norm_div,Real.norm_natCast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    simpa only [Real.norm_eq_abs] using
      FiniteInformation.labelDilationDefect_abs_le k (g ∘ Nat.maxPrimeFac) n
  · have he : Nat.maxPrimeFac (k*n) = Nat.maxPrimeFac n := by
      rw [Nat.maxPrimeFac_mul hk.ne' hn,max_eq_right]
      exact (Nat.maxPrimeFac_le (n := k)).trans (by omega)
    have hz : FiniteInformation.labelDilationDefect k (g ∘ Nat.maxPrimeFac) n = 0 := by
      simp [FiniteInformation.labelDilationDefect,Function.comp_apply,he]
    rw [hz,zero_div,norm_zero]
    exact smoothReciprocal_nonneg k n

/-- The total harmonic dilation defect is O(log k), uniformly over arbitrary
relabellings of the largest prime factor. This is not a Tauberian theorem. -/
theorem maxPrimeFac_label_total_harmonic_defect_le_log {A : Type*} (g : ℕ → A)
    (k : ℕ) (hk : 0<k) :
    (∑' n, ‖FiniteInformation.labelDilationDefect k (g ∘ Nat.maxPrimeFac) n/(n : ℝ)‖) ≤
      Real.exp 4 * (1+Real.log (k+1 : ℝ)/Real.log 2) := by
  exact (Summable.tsum_le_tsum (fun n => maxPrimeFac_label_harmonic_defect_le g k n hk)
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => maxPrimeFac_label_harmonic_defect_le g k n hk) (summable_smoothReciprocal k))
    (summable_smoothReciprocal k)).trans (smoothReciprocal_tsum_le_log k hk)

#print axioms maxPrimeFac_label_total_harmonic_defect_le_log
#print axioms primeEulerProduct_le_log
#print axioms smoothReciprocal_tsum_le_log
end Erdos371
