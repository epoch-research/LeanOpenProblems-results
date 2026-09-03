import Submission.PoolSupplyBlocks

/-!
# The retained-pool rejection budget

The long-range leading constant is below 0.98. All multiplier-block
errors are absorbed relative to the actual fixed reciprocal pool mass.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 5000000

lemma poolLongLimit_lt : scaledProductLongLimit poolLongCoefficient 8040000 10000007 < (49/50 : ℝ) := by
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hfrac : (1/1000000 : ℝ)/Real.log 2 ≤ 2/1000000 := by
    exact (div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ)<1/2) hlog).trans_eq (by norm_num)
  unfold scaledProductLongLimit
  norm_num only [Nat.cast_ofNat]
  have hp := poolLongCoefficient_pos.le
  calc
    _ ≤ (64*40000021)*(poolLongCoefficient+(2/1000000 : ℝ))*
        (1/(128*(8040000 : ℝ))-1/(128*(10000007 : ℝ))) := by gcongr <;> norm_num
    _ < _ := by norm_num [poolLongCoefficient]

lemma eventually_pool_block_coefficient :
    ∀ᶠ m : ℕ in atTop,
      (1+1/(2 : ℝ)^10)*(256*(m : ℝ)+2)*(2 : ℝ)^10/(128*(8040000 : ℝ)*m+1)^3 ≤
        (1/1000000 : ℝ)*poolTotientMass (widePairPool 10000000 m) := by
  let W := widePairMassDenom 10000000
  have hW : 0 < W := widePairMassDenom_pos 10000000
  have hWR : (0 : ℝ)<W := by exact_mod_cast hW
  filter_upwards [eventually_ge_atTop (1000000*W*600000+1)] with m hm
  have hm1 : 1 ≤ m := by omega
  have hmR : (1000000 : ℝ)*W*600000+1 ≤ m := by exact_mod_cast hm
  have hnum : (1+1/(2 : ℝ)^10)*(256*(m : ℝ)+2)*(2 : ℝ)^10 ≤ 600000*((m : ℝ)+1) := by
    norm_num
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hden : ((m : ℝ)+1)^3 ≤ (128*(8040000 : ℝ)*m+1)^3 := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  calc
    _ ≤ 600000*((m : ℝ)+1)/((m : ℝ)+1)^3 := div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 600000/((m : ℝ)+1)^2 := by field_simp
    _ ≤ 1/(1000000*(W : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ)<((m : ℝ)+1)^2) (by positivity : (0 : ℝ)<1000000*W)).mpr
      have hm0 := Nat.cast_nonneg (α := ℝ) m
      nlinarith only [hmR,hm0,sq_nonneg (m : ℝ)]
    _ = (1/1000000 : ℝ)*(1/(W : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (widePairPool_mass_lower 10000000 m hm1) (by norm_num)

/-- A uniform bound over the bounded enlargement used for prime supply. -/
theorem eventually_pool_long_rejection_bound :
    ∀ᶠ m : ℕ in atTop, ∀ X : ℕ,
      independentN 40000020 m ≤ X → X ≤ independentN 40000021 m →
      Real.log (X : ℝ)*(∑ c ∈ widePairPool 10000000 m,
        ((hyperbolicPrimePairPool c (X/c) (2^(128*8040000*m)) (2^(128*10000007*m))).card : ℝ)) ≤
          (49/50 : ℝ)*(X : ℝ)*poolTotientMass (widePairPool 10000000 m) := by
  obtain ⟨C,hC,HC⟩ := exists_pool_long_raw_bound
  have hbudget : ∀ᶠ m : ℕ in atTop, scaledProductLongBudget poolLongCoefficient 8040000 10000007 C m ≤ (49/50 : ℝ) :=
    (tendsto_scaledProductLongBudget _ C _ _ (by decide) (by decide)).eventually
      (eventually_le_nhds poolLongLimit_lt)
  filter_upwards [HC,hbudget,eventually_pool_block_coefficient,eventually_ge_atTop 1] with m hraw hbudget hblock hm
  intro X hXlo hXhi
  let V := poolTotientMass (widePairPool 10000000 m)
  let Δ : ℝ := 1/(128*(8040000 : ℝ)*m-1)-1/(128*(10000007 : ℝ)*m-1)
  let T : ℝ := Real.log 2*Δ+2*C/(128*(8040000 : ℝ)*m)^2
  let U : ℝ := poolLongCoefficient/(Real.log 2)^2*T+(1/1000000 : ℝ)/(Real.log 2)^2*Δ
  let L : ℝ := 64*40000021*(m : ℝ)*Real.log 2
  let cnt : ℝ := ∑ c ∈ widePairPool 10000000 m,
    ((hyperbolicPrimePairPool c (X/c) (2^(128*8040000*m)) (2^(128*10000007*m))).card : ℝ)
  have hV : 0 ≤ V := poolTotientMass_nonneg _
  have hcnt : 0 ≤ cnt := sum_nonneg (fun c _ => Nat.cast_nonneg _)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr (one_div_le_one_div_of_le (by nlinarith) (by nlinarith))
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hU : 0 ≤ U := by have := poolLongCoefficient_pos.le; dsimp [U]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have he : L*U=scaledProductLongBudget poolLongCoefficient 8040000 10000007 C m :=
    scaledProductLongBudget_identity _ C _ _ m (by decide) (by decide) hm
  have herr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hblock (show 0 ≤ (X : ℝ)/(Real.log 2)^2 by positivity)) hΔ
  have hbound : cnt ≤ (X : ℝ)*V*U := by
    have h := (hraw X hXlo hXhi).trans (_root_.add_le_add le_rfl (by convert herr using 1; dsimp [Δ]; simp only [div_mul_eq_div_div]; ring))
    convert h using 1; dsimp [V,U,T,Δ]; ring
  have h := mul_le_mul (scaled_supply_log_upper m X hXhi) hbound hcnt hL
  have hb := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ (X : ℝ)*V by positivity)
  have hid : L*((X : ℝ)*V*U)=(X : ℝ)*V*scaledProductLongBudget poolLongCoefficient 8040000 10000007 C m := by
    rw [← he]
    ring
  rw [hid] at h
  apply (h.trans hb).trans_eq
  ring

/-- The short tail is supplied by the already proved pointwise sieve. -/
theorem eventually_pool_rough_rejection_bound :
    ∀ᶠ m : ℕ in atTop, ∀ X : ℕ,
      independentN 40000020 m ≤ X → X ≤ independentN 40000021 m →
      Real.log (X : ℝ)*(∑ c ∈ widePairPool 10000000 m,
        ((roughProgressionPrimes c (independentN 16080000 m) X).card : ℝ)) ≤
          (99/100 : ℝ)*(X : ℝ)*poolTotientMass (widePairPool 10000000 m) := by
  filter_upwards [eventually_pool_long_rejection_bound,eventually_scaled_band_short_tail,eventually_ge_atTop 1]
    with m hlong hshort hm
  intro X hXlo hXhi
  let V := poolTotientMass (widePairPool 10000000 m)
  have hpos : 0 ≤ (X : ℝ)*V := mul_nonneg (Nat.cast_nonneg X) (poolTotientMass_nonneg _)
  have hpoint (c : ℕ) (hc : c ∈ widePairPool 10000000 m) :
      ((roughProgressionPrimes c (independentN 16080000 m) X).card : ℝ) ≤
        ((hyperbolicPrimePairPool c (X/c) (2^(128*8040000*m)) (2^(128*10000007*m))).card : ℝ)+
        ((hyperbolicPrimePairPool c (X/c) (2^(128*10000007*m)) (X/c)).card : ℝ) := by
    have hb := widePairPool_bounds 10000000 m c hc
    exact rough_progression_card_le_long_short c (independentN 16080000 m) X (2^(128*10000007*m))
      (by omega) (widePairPool_smooth_odd 10000000 16080000 m c (by decide) (by decide) hm hc).1
      (not_prime_two_pow _ (by omega))
  have hsum := mul_le_mul_of_nonneg_left (sum_le_sum hpoint) (Real.log_natCast_nonneg X)
  rw [sum_add_distrib,mul_add] at hsum
  have hs : Real.log (X : ℝ)*(∑ c ∈ widePairPool 10000000 m,
      ((hyperbolicPrimePairPool c (X/c) (2^(128*10000007*m)) (X/c)).card : ℝ)) ≤
        (11/62500 : ℝ)*(X : ℝ)*V := by
    rw [mul_sum]
    apply (sum_le_sum (fun c hc => hshort X c hXlo hXhi
      (widePairPool_bounds 10000000 m c hc).2.1 (widePairPool_bounds 10000000 m c hc).2.2)).trans_eq
    dsimp [V,poolTotientMass]
    rw [mul_sum]
    exact sum_congr rfl (fun c _ => by ring)
  have hl := hlong X hXlo hXhi
  change _ ≤ (49/50 : ℝ)*(X : ℝ)*V at hl
  change _ ≤ (99/100 : ℝ)*(X : ℝ)*V
  nlinarith only [hsum,hs,hl,hpos]

end Erdos821.AnalyticSieve
