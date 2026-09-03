import Submission.PrimeWinnerFlux
import Submission.PrimeWinnerEnergyLogSavings

/-! Unconditional sublinear prime-winner energy in a logarithmically growing
cofactor range. This does not estimate the remaining bulk prime groups. -/

namespace Erdos371
open Finset Filter
open FiniteSieve
open scoped Topology

lemma primeWinnerEnergyAbove_top_ratio_bound (B K N : ℕ) (u : ℝ)
    (hN : 1 < N) (hu0 : 0 ≤ u) (hu : u ≤ 1/8)
    (hcut : (N : ℝ)^(1-u) ≤ B) (hsize : N ≤ K*(B+1)) :
    primeWinnerEnergyAbove B N / N ≤ (2*K+1 : ℝ) *
      (largePairConstant*(u+1/Real.log N)^2 +
        (2 : ℝ)^65*(N : ℝ)^(-1/2 : ℝ) + 1/N) := by
  have hsub : bothAboveSet B N ⊆ bothLargePrimeSet N u := by
    intro n hn
    obtain ⟨hnN,hp,hq⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hnN, hcut.trans_lt (by exact_mod_cast hp),
      hcut.trans_lt (by exact_mod_cast hq)⟩
  have hc : ((bothAboveSet B N).card : ℝ) ≤ (bothLargePrimeSet N u).card :=
    Nat.cast_le.mpr (card_le_card hsub)
  have hL := (primeWinnerL1Above_le_bothAbove B N).trans (add_le_add hc (le_refl 1))
  have hL' := div_le_div_of_nonneg_right hL (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div] at hL'
  have htop := bothLargePrimeSet_ratio_bound N u hN hu0 hu
  have hE := div_le_div_of_nonneg_right (primeWinnerEnergyAbove_bound B K N hsize)
    (Nat.cast_nonneg (α := ℝ) N)
  rw [mul_div_assoc] at hE
  exact hE.trans (mul_le_mul_of_nonneg_left
    (hL'.trans (add_le_add htop (le_refl _))) (by positivity))

lemma div_cutoff_ge_power_of_mul_le_rpow (K N : ℕ) (u : ℝ)
    (hK : 0 < K) (hKN : K ≤ N) (hpow : (2*K : ℝ) ≤ (N : ℝ)^u) :
    (N : ℝ)^(1-u) ≤ ((N/K : ℕ) : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hK.trans_le hKN
  have hdiv : 1 ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr (by simpa using hKN)
  have hfloor : N ≤ 2*K*(N/K) := by
    have hh := Nat.mod_lt N hK
    have he := Nat.mod_add_div N K
    nlinarith
  have hfloor' : (N : ℝ) ≤ 2*K*((N/K : ℕ) : ℝ) := by exact_mod_cast hfloor
  have hprod : (N : ℝ)^(1-u)*(N : ℝ)^u = N := by
    rw [← Real.rpow_add hN0]
    simp
  have hm := mul_le_mul_of_nonneg_left hpow
    (Real.rpow_nonneg (Nat.cast_nonneg N) (1-u))
  rw [hprod] at hm
  exact le_of_mul_le_mul_left
    (by nlinarith : (2*K : ℝ)*(N : ℝ)^(1-u) ≤ 2*K*((N/K : ℕ) : ℝ))
    (by positivity)

noncomputable def logarithmicCofactorCutoff (N : ℕ) : ℕ := ⌊Real.log N⌋₊

lemma logarithmicCofactorCutoff_tendsto_atTop :
    Tendsto logarithmicCofactorCutoff atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

noncomputable def logarithmicCofactorExponent (N : ℕ) : ℝ :=
  Real.log (2*Real.log N)/Real.log N

lemma logarithmicCofactorExponent_tendsto_zero :
    Tendsto logarithmicCofactorExponent atTop (nhds 0) := by
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun N : ℕ => Real.log 2/Real.log N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hL
  have h2 : Tendsto (fun N : ℕ => Real.log (Real.log N)/Real.log N)
      atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp hL
  have ht := h1.add h2
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [hL.eventually_gt_atTop 0] with N hN
  simp [logarithmicCofactorExponent, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN.ne', add_div]

lemma logarithmicCofactor_cutoff_data :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log N ∧
      0 < logarithmicCofactorCutoff N ∧
      0 ≤ logarithmicCofactorExponent N ∧
      logarithmicCofactorExponent N ≤ 1/8 ∧
      (N : ℝ)^(1-logarithmicCofactorExponent N) ≤
        ((N/logarithmicCofactorCutoff N : ℕ) : ℝ) := by
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hL.eventually_ge_atTop 1,
    logarithmicCofactorExponent_tendsto_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1/8),
    eventually_gt_atTop (1 : ℕ)] with N hL hsmall hN
  have hL0 : 0 < Real.log N := by linarith
  have hK : 0 < logarithmicCofactorCutoff N := by
    exact (Nat.one_le_floor_iff _).mpr hL
  have hKle : (logarithmicCofactorCutoff N : ℝ) ≤ Real.log N :=
    Nat.floor_le hL0.le
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hKN : logarithmicCofactorCutoff N ≤ N := by
    have hh : Real.log (N : ℝ) ≤ N := (Real.log_le_sub_one_of_pos hN0).trans (by linarith)
    exact_mod_cast hKle.trans hh
  have hpos : 0 ≤ logarithmicCofactorExponent N :=
    div_nonneg (Real.log_nonneg (by linarith)) hL0.le
  have hpow : (N : ℝ)^(logarithmicCofactorExponent N) = 2*Real.log N := by
    rw [Real.rpow_def_of_pos hN0]
    unfold logarithmicCofactorExponent
    rw [mul_div_cancel₀ _ hL0.ne']
    exact Real.exp_log (by positivity)
  refine ⟨hL,hK,hpos,hsmall,?_⟩
  apply div_cutoff_ge_power_of_mul_le_rpow _ _ _ hK hKN
  rw [hpow]
  linarith

lemma log_affine_square_div_tendsto_zero :
    Tendsto (fun x : ℝ => (Real.log (2*x)+1)^2/x) atTop (nhds 0) := by
  have h1 : Tendsto (fun x : ℝ => (Real.log 2+1)^2/x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun x : ℝ => Real.log x/x) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have h3 : Tendsto (fun x : ℝ => (Real.log x)^2/x) atTop (nhds 0) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have ht := (h1.add (h2.const_mul (2*(Real.log 2+1)))).add h3
  simp only [mul_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne']
  ring

/-- Genuine sublinear energy for winning primes above N/floor(log N).
Unlike the fixed-cofactor theorem, the permitted cofactor range tends to
infinity. No bound for the complementary prime groups is asserted. -/
theorem primeWinnerEnergyAbove_logarithmic_cofactor_tendsto :
    Tendsto (fun N : ℕ =>
      primeWinnerEnergyAbove (N/logarithmicCofactorCutoff N) N / N)
      atTop (nhds 0) := by
  have hL : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmain := (log_affine_square_div_tendsto_zero.comp hL).const_mul
    (3*largePairConstant)
  have herr := (log_nat_pow_div_rpow_tendsto_zero 1 (1/2) (by norm_num)).const_mul
    (3*(2 : ℝ)^65)
  have hend : Tendsto (fun N : ℕ => 3*Real.log N/N) atTop (nhds 0) := by
    simpa only [pow_one,Real.rpow_one,mul_div_assoc,mul_zero] using
      (log_nat_pow_div_rpow_tendsto_zero 1 1 (by norm_num)).const_mul 3
  have ht := (hmain.add herr).add hend
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => by
    unfold primeWinnerEnergyAbove; positivity)) _ ht
  filter_upwards [logarithmicCofactor_cutoff_data, eventually_gt_atTop (1 : ℕ)]
    with N hdata hN
  obtain ⟨hL,hK,hupos,hu,hcut⟩ := hdata
  let K := logarithmicCofactorCutoff N
  let u := logarithmicCofactorExponent N
  have hL0 : 0 < Real.log N := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsize : N ≤ K*(N/K+1) := by
    have hh := Nat.mod_lt N hK
    have he := Nat.mod_add_div N K
    nlinarith
  have hcoef : (2*K+1 : ℝ) ≤ 3*Real.log N := by
    have hk : (K : ℝ) ≤ Real.log N := Nat.floor_le hL0.le
    linarith
  have hb := primeWinnerEnergyAbove_top_ratio_bound (N/K) K N u hN hupos hu hcut hsize
  have hC : 0 ≤ largePairConstant := by unfold largePairConstant; positivity
  have hnonneg : 0 ≤ largePairConstant*(u+1/Real.log N)^2 +
      (2 : ℝ)^65*(N : ℝ)^(-1/2 : ℝ)+1/N := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcoef hnonneg
  have hexp : (N : ℝ)^(-1/2 : ℝ) = 1/(N : ℝ)^(1/2 : ℝ) := by
    rw [show (-1/2 : ℝ) = -(1/2) by ring, Real.rpow_neg (Nat.cast_nonneg N)]
    exact (one_div _).symm
  apply (hb.trans hmul).trans_eq
  rw [hexp]
  dsimp only [u,logarithmicCofactorExponent]
  simp only [pow_one,Function.comp_apply]
  field_simp

#print axioms primeWinnerEnergyAbove_top_ratio_bound
#print axioms logarithmicCofactor_cutoff_data
#print axioms primeWinnerEnergyAbove_logarithmic_cofactor_tendsto
end Erdos371
