import Submission.PoolBandBudget

/-! Variable-band rejection bounds for the actual retained multiplier pool. -/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 6000000

noncomputable def poolBandCoefficient (b : ℕ) : ℝ :=
  (2*(100000000 : ℝ)/(b : ℝ))*(1+1/(2 : ℝ)^10)^2

lemma poolBandCoefficient_nonneg (b : ℕ) : 0 ≤ poolBandCoefficient b := by
  unfold poolBandCoefficient
  positivity

theorem eventually_pool_band_rejection_bound (u v b l : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ 10000007) (hu3 : 20000011 ≤ 3*u)
    (hb : 1 ≤ b) (hbt : b < 200000000) (hl : 1 ≤ l) (hlevel : 2*b+1 ≤ l+100000000)
    (hscale : l*v < 100000000*(20000009-v)) (hroughscale : b*v < 100000000*10000000)
    (J : ℝ) (hlimit : scaledProductLongLimit (poolBandCoefficient b) u v < J) :
    ∀ᶠ m : ℕ in atTop, ∀ X : ℕ,
      independentN 40000020 m ≤ X → X ≤ independentN 40000021 m →
      Real.log (X : ℝ)*(∑ c ∈ widePairPool 10000000 m,
        ((hyperbolicPrimePairPool c (X/c) (2^(128*u*m)) (2^(128*v*m))).card : ℝ)) ≤
          J*(X : ℝ)*poolTotientMass (widePairPool 10000000 m) := by
  obtain ⟨C,hC,K₀,HK⟩ := exists_wide_pool_hyperbolic_bound 1 b 3 l 200000000 100000000 10 10 3
    (by decide) hb (by decide) hl (by decide) hbt hlevel 1 (by norm_num)
  have hbudget : ∀ᶠ m : ℕ in atTop, scaledProductLongBudget (poolBandCoefficient b) u v C m ≤ J :=
    (tendsto_scaledProductLongBudget _ C u v hu (hu.trans huv)).eventually (eventually_le_nhds hlimit)
  filter_upwards [hbudget,eventually_pool_band_product_lower l v hv hscale,
    eventually_pool_band_sieve_cutoff b v hroughscale,eventually_pool_block_coefficient_uniform,
    eventually_ge_atTop (max 1000000 K₀)] with m hbudget hlower hrough hblock hm
  have hm0 : 1000000 ≤ m := (le_max_left _ _).trans hm
  have hm1 : 1 ≤ m := by omega
  have hmK : K₀ ≤ m := (le_max_right _ _).trans hm
  intro X hXlo hXhi
  have hsum : 128*u*m+128*(v-u)*m=128*v*m := by
    have hh := congrArg (fun n : ℕ => 128*n*m) (Nat.add_sub_of_le huv)
    nlinarith only [hh]
  have hsumR : 128*(u : ℝ)*m+128*((v-u : ℕ) : ℝ)*m=128*(v : ℝ)*m := by
    rw [Nat.cast_sub huv]
    ring
  have hscale0 : ∀ i ∈ range (poolMultiplierL m), ∀ j ∈ range (2^10),
      let D := multiplierUpper (poolMultiplierK m+i) 10 j
      let H := X/multiplierLower (poolMultiplierK m+i) 10 j
      cofactorScale 3 (2*cofactorDyadicIndex 100000000 (128*v*m)) ≤ H/2^(128*v*m) ∧
      cofactorScale l (2*cofactorDyadicIndex 100000000 (128*v*m)) ≤ D*(H/2^(128*v*m)) ∧
      D*(H/2^(128*u*m)) ≤ cofactorScale 200000000 (2*cofactorDyadicIndex 100000000 (128*u*m+1)) := by
    intro i hi j hj
    have hkr : 10 ≤ poolMultiplierK m+i := by unfold poolMultiplierK; omega
    have hCup : multiplierLower (poolMultiplierK m+i) 10 j ≤ 2^(64*20000004*m+1) := by
      apply (multiplierLower_le_upper _ _ _).trans
      apply (multiplierUpper_upper _ _ _ (mem_range.mp hj) hkr).trans
      rw [← poolMultiplier_end m hm1]
      exact Nat.pow_le_pow_right (by decide) (by have := mem_range.mp hi; omega)
    exact ⟨pool_band_short_prefix v m X _ hv hm0 hXlo (multiplierLower_pos _ _ _) hCup,
      hlower X _ _ hXlo (multiplierLower_pos _ _ _) (multiplierLower_le_upper _ _ _) hCup,
      pool_band_product_upper u m X _ _ hu3 hXhi (multiplierUpper_le_two_lower _ _ _)⟩
  have hK : K₀ ≤ 128*u*m := by
    have h := Nat.mul_le_mul_right m hu
    nlinarith only [h,hmK]
  have hK2 : 2 ≤ 128*u*m := by
    have h := Nat.mul_pos hu hm1
    nlinarith only [h]
  have h := HK (128*u*m) (128*(v-u)*m) X (poolMultiplierK m) (poolMultiplierL m)
    hK hK2 (by unfold poolMultiplierK; omega) (widePairPool 10000000 m)
    (poolMultiplier_support m hm1) (by rw [hsum]; exact widePairPool_rough_below m _ hrough)
    (by rw [hsum]; exact hscale0)
  rw [hsum] at h
  simp only [Nat.cast_mul,Nat.cast_ofNat] at h
  rw [hsumR] at h
  let V := poolTotientMass (widePairPool 10000000 m)
  let Δ : ℝ := 1/(128*(u : ℝ)*m-1)-1/(128*(v : ℝ)*m-1)
  let T : ℝ := Real.log 2*Δ+2*C/(128*(u : ℝ)*m)^2
  let cnt : ℝ := ∑ c ∈ widePairPool 10000000 m,
    ((hyperbolicPrimePairPool c (X/c) (2^(128*u*m)) (2^(128*v*m))).card : ℝ)
  have hV : 0 ≤ V := poolTotientMass_nonneg _
  have hcnt : 0 ≤ cnt := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hum : (1 : ℝ) ≤ (u : ℝ)*m := by exact_mod_cast Nat.mul_pos hu hm1
  have huvm : (u : ℝ)*m ≤ (v : ℝ)*m := by exact_mod_cast Nat.mul_le_mul_right m huv
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr (one_div_le_one_div_of_le (by nlinarith) (by nlinarith))
  have hT : 0 ≤ T := by dsimp [T]; positivity [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hraw : cnt ≤
      (poolBandCoefficient b*(X : ℝ)*(∑ c ∈ widePairPool 10000000 m, (c : ℝ)⁻¹)/(Real.log 2)^2)*T+
      ((1+1/(2 : ℝ)^10)*(X : ℝ)*(256*(m : ℝ)+2)*(2 : ℝ)^10/
        ((Real.log 2)^2*(128*(u : ℝ)*m+1)^3))*Δ := by
    convert h using 1
    dsimp [poolBandCoefficient,poolMultiplierL,T,Δ]
    push_cast
    ring
  have hrec := mul_le_mul_of_nonneg_left
    (sum_inverse_le_poolTotientMass (widePairPool 10000000 m)
      (fun c hc => (by have := (widePairPool_bounds 10000000 m c hc).1; omega)))
    (show 0 ≤ poolBandCoefficient b*(X : ℝ)/(Real.log 2)^2*T by
      have := poolBandCoefficient_nonneg b; positivity)
  have herr := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hblock u hu)
    (show 0 ≤ (X : ℝ)/(Real.log 2)^2 by positivity)) hΔ
  have hfinal : cnt ≤
      (poolBandCoefficient b*(X : ℝ)*V/(Real.log 2)^2)*T+
      ((1/1000000 : ℝ)*(X : ℝ)*V/(Real.log 2)^2)*Δ := by
    apply hraw.trans
    convert _root_.add_le_add hrec herr using 1 <;> dsimp [V] <;>
      (try simp only [div_mul_eq_div_div]) <;> ring
  exact pool_scaled_weighted_budget u v m X (poolBandCoefficient b) C V cnt J hu huv hm1
    (poolBandCoefficient_nonneg b) hC.le hV hcnt hXhi hfinal hbudget

end Erdos821.AnalyticSieve
