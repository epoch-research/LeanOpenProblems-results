import Submission.BlockCompositeScales

/-!
# Multiplicity lower bounds from the blockwise structured sieve

This gives an unconditional sufficient parameter criterion. It does not
assert that the criterion reaches exponents tending to one.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma eventually_block_total_error_divisor (r t b h D : ℕ)
    (heq : r+b+h=t) (hb : 1 ≤ b) (hh : 1 ≤ h) (hD : 0 < D) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (independentN t m : ℝ)*
        (blockSieveError r b h m+
          2*((t-1).choose r : ℝ)*Real.sqrt (independentN t m : ℝ)) ≤
        (independentN t m : ℝ)/(D : ℝ)*primeProductReciprocalMass r m := by
  have he : ∀ᶠ m : ℕ in atTop, ∀ j ∈ range h,
      Real.log (independentN t m : ℝ)*
        (independentSieveError r (blockCutoff b h j) (j+1) m+
          2*((t-1).choose r : ℝ)*Real.sqrt (independentN t m : ℝ)) ≤
        (independentN t m : ℝ)/(D*h : ℕ)*primeProductReciprocalMass r m := by
    rw [eventually_all_finset]
    intro j hj
    have hc := blockCutoff_properties r t b h j heq (mem_range.mp hj)
    exact eventually_independent_total_error_divisor r t (blockCutoff b h j) (j+1) (D*h)
      hc.2 (hb.trans hc.1) (Nat.mul_pos hD hh)
  filter_upwards [he] with m he
  let N := independentN t m
  let S : ℝ := 2*((t-1).choose r : ℝ)*Real.sqrt (N : ℝ)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hhpos : (0 : ℝ) < h := by exact_mod_cast hh
  calc
    _ ≤ Real.log (N : ℝ)*(blockSieveError r b h m+(h : ℝ)*S) := by
      apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg N)
      have hs := mul_le_mul_of_nonneg_right hhR hS
      dsimp only [S,N] at hs ⊢
      linarith only [hs]
    _ = ∑ j ∈ range h, Real.log (N : ℝ)*
        (independentSieveError r (blockCutoff b h j) (j+1) m+S) := by
      rw [← mul_sum,sum_add_distrib]
      simp only [sum_const,nsmul_eq_mul,card_range,blockSieveError]
    _ ≤ ∑ _j ∈ range h, (N : ℝ)/(D*h : ℕ)*primeProductReciprocalMass r m := sum_le_sum he
    _ = _ := by
      simp only [sum_const,nsmul_eq_mul,card_range,Nat.cast_mul]
      dsimp only [N]
      field_simp

lemma blockMainLimit_nonneg (t b h : ℕ) : 0 ≤ blockMainLimit t b h := by
  unfold blockMainLimit
  apply sum_nonneg
  intro j hj
  unfold independentMainLimit
  positivity

theorem eventually_block_chebyshev_retained_weight (r t b h D : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b) (hh : 1 ≤ h)
    (hcap : t+5 ≤ 5*b) (hD : 0 < D)
    (hc : blockMainLimit t b h+3/(D : ℝ) < chebyshevRatioConstant) :
    ∀ᶠ m : ℕ in atTop,
      (independentN t m : ℝ)/(D : ℝ)*primeProductReciprocalMass r m ≤
        ((t-1).choose r : ℝ)*Real.log (independentN t m : ℝ)*
          ((smoothStructuredPrimes r m (independentN t m) (independentN b m)).card : ℝ) := by
  let a := blockMainLimit t b h
  have ha0 : 0 ≤ a := blockMainLimit_nonneg t b h
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have ha : a < a+1/(D : ℝ) := lt_add_of_pos_right a (by positivity)
  filter_upwards [eventually_product_mangoldt_lower_constant r t hrt
      (a+3/(D : ℝ)) (by positivity) hc,
    eventually_block_total_error_divisor r t b h D heq (by omega) hh hD,
    eventually_block_sieve_main_constant r t b h heq hb (a+1/(D : ℝ)) ha,
    eventually_ge_atTop (max 2 r),eventually_block_endpoint_all r t b h heq hb,
    eventually_cofactorBlock_mass_all h] with m hw he hmain hm hend hmass
  have hw' : (a+3*(1/(D : ℝ)))*(2^(64*t*m) : ℝ)*primeProductReciprocalMass r m ≤
      ∑ d ∈ primeProductModuli r m, residueOneMangoldt d (2^(64*t*m)) := by
    simpa only [progressionScaleN,mul_assoc,Nat.cast_pow,Nat.cast_ofNat,mul_one_div] using hw
  have hr := block_rough_count_le r t b h m heq hb hh hcap hm hend hmass
  have hg := flexible_smooth_weight_retained r t m (independentN b m) (by omega)
    a (1/(D : ℝ)) (blockSieveMain t b h m) (blockSieveError r b h m) hw' hr
    (by simpa only [independentN,Nat.cast_pow,Nat.cast_ofNat] using hmain)
    (by simpa only [independentN,Nat.cast_pow,Nat.cast_ofNat,div_eq_mul_inv,
      one_mul,mul_comm,mul_left_comm,mul_assoc] using he)
  simpa only [independentN,Nat.cast_pow,Nat.cast_ofNat,div_eq_mul_inv,
    one_mul,mul_comm,mul_left_comm,mul_assoc] using hg

theorem eventually_block_chebyshev_smooth_family (r t b h D : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b) (hh : 1 ≤ h)
    (hcap : t+5 ≤ 5*b) (hD : 0 < D)
    (hc : blockMainLimit t b h+3/(D : ℝ) < chebyshevRatioConstant) :
    ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2^(64*t*m) ∧ p-1 ∈ Nat.smoothNumbers (2^(64*b*m))) ∧
      2^(64*t*m) ≤ flexibleStructuredCountConstant r t D*(m+1)^(r+1)*P.card := by
  filter_upwards [eventually_product_reciprocal_supply r,
    eventually_block_chebyshev_retained_weight r t b h D heq hrt hb hh hcap hD hc] with m hm hw
  refine ⟨smoothStructuredPrimes r m (independentN t m) (independentN b m),?_,
    flexible_independent_count_of_weight r t b m D hD hm hw⟩
  intro p hp
  obtain ⟨hpP,hps⟩ := mem_filter.mp hp
  obtain ⟨hpN,_⟩ := mem_filter.mp hpP
  have hpdata := Nat.mem_primesBelow.mp hpN
  exact ⟨hpdata.2,by change p ≤ independentN t m; omega,hps⟩

/-- A fixed-exponent theorem with one sieve length per cofactor block. -/
theorem infinite_g_gt_block_parameters (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b) (hh : 1 ≤ h)
    (hcap : t+5 ≤ 5*b) (hc : blockMainLimit t b h < chebyshevRatioConstant)
    (γ : ℝ) (hγ : γ < 1-(b : ℝ)/t) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨D,hD⟩ := exists_nat_gt (max 1 (3/(chebyshevRatioConstant-blockMainLimit t b h)))
  have hD1 : (1 : ℝ) < D := (le_max_left _ _).trans_lt hD
  have hDpos : (0 : ℝ) < D := by linarith
  have hDn : 0 < D := by exact_mod_cast hDpos
  have hgap : 3/(D : ℝ) < chebyshevRatioConstant-blockMainLimit t b h := by
    apply (div_lt_iff₀ hDpos).mpr
    have h := (div_lt_iff₀ (sub_pos.mpr hc)).mp ((le_max_right _ _).trans_lt hD)
    linarith only [h]
  have hco : blockMainLimit t b h+3/(D : ℝ) < chebyshevRatioConstant := by linarith
  apply infinite_g_gt_of_eventual_polynomial_count (64*t) (64*b) 1
    (flexibleStructuredCountConstant r t D) (r+1) (by omega) ?_ γ ?_
  · filter_upwards [eventually_block_chebyshev_smooth_family r t b h D
      heq hrt hb hh hcap hDn hco] with m hm
    simpa only [one_mul] using hm
  · simpa only [Nat.cast_mul,Nat.cast_ofNat,
      mul_div_mul_left _ _ (by norm_num : (64 : ℝ) ≠ 0)] using hγ

end Erdos821
