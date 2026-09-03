import Submission.ProductSupplyBudget

/-!
# Fixed scales for the two-range product-sieve supply
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma product_supply_first_threshold (m H : ℕ) (hm : 10000 ≤ m)
    (hH : 2^(128*100008*m) ≤ H) :
    cofactorScale 12750 (2*cofactorDyadicIndex 200003 (128*94000*m)) ≤ H/2^(128*94000*m) := by
  have hh := (cofactorDyadicIndex_bounds 200003 (128*94000*m) (by decide)).2
  have he : 6528000*cofactorDyadicIndex 200003 (128*94000*m) ≤ 769024*m := by
    nlinarith only [hh,hm]
  have hs : cofactorScale 12750 (2*cofactorDyadicIndex 200003 (128*94000*m)) ≤ 2^(769024*m) := by
    rw [cofactorScale_eq]
    apply Nat.pow_le_pow_right (by decide)
    nlinarith only [he]
  apply hs.trans
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2^(128*94000*m))).mpr
  apply le_trans _ hH
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  omega

lemma product_supply_second_threshold (m H : ℕ) (hm : 10000 ≤ m)
    (hH : 2^(128*100008*m) ≤ H) :
    cofactorScale 3 (2*cofactorDyadicIndex 400003 (128*100007*m)) ≤ H/2^(128*100007*m) := by
  have hh := (cofactorDyadicIndex_bounds 400003 (128*100007*m) (by decide)).2
  have he : 1536*cofactorDyadicIndex 400003 (128*100007*m) ≤ 128*m := by
    nlinarith only [hh,hm]
  have hs : cofactorScale 3 (2*cofactorDyadicIndex 400003 (128*100007*m)) ≤ 2^(128*m) := by
    rw [cofactorScale_eq]
    apply Nat.pow_le_pow_right (by decide)
    nlinarith only [he]
  apply hs.trans
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2^(128*100007*m))).mpr
  apply le_trans _ hH
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  omega

lemma product_supply_hyperbola_upper (m H : ℕ) (hH : H ≤ 2^(128*100011*m)) :
    H ≤ 2^(2*(128*88850*m)) := by
  apply hH.trans
  exact Nat.pow_le_pow_right (by decide) (by omega)

lemma product_supply_smooth_cutoff_not_prime (m : ℕ) (hm : 1 ≤ m) :
    ¬(independentN 177700 m).Prime := by
  apply not_prime_two_pow
  omega

noncomputable def productSupplyTailError (m : ℕ) : ℝ :=
  (2 : ℝ)^(512*m)*((2 : ℝ)^(6400448*m)+(2 : ℝ)^(1600112*m)+1)

lemma productSupplyTailError_nonneg (m : ℕ) : 0 ≤ productSupplyTailError m := by
  unfold productSupplyTailError
  positivity

lemma productSupplyTailError_le (m : ℕ) : productSupplyTailError m ≤ 3*(2 : ℝ)^(6400960*m) := by
  have h1 : (2 : ℝ)^(1600112*m) ≤ (2 : ℝ)^(6400448*m) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (1 : ℝ) ≤ 2^(6400448*m) := one_le_pow₀ (by norm_num)
  have hh := mul_le_mul_of_nonneg_left (_root_.add_le_add (_root_.add_le_add (le_refl ((2 : ℝ)^(6400448*m))) h1) h2)
    (show (0 : ℝ) ≤ 2^(512*m) by positivity)
  have he : (2 : ℝ)^(512*m)*(2 : ℝ)^(6400448*m)=(2 : ℝ)^(6400960*m) := by
    rw [← pow_add]
    congr 1
    omega
  unfold productSupplyTailError
  nlinarith only [hh,he]

lemma eventually_product_supply_tail_error :
    ∀ᶠ m : ℕ in atTop, ∀ X H : ℕ, X ≤ independentN 400021 m →
      2^(128*100008*m) ≤ H →
        Real.log (X : ℝ)*productSupplyTailError m ≤ (H : ℝ)/10000 := by
  filter_upwards [eventually_nat_poly_le_two_pow 1 (30000*25601344) 1] with m hm
  intro X H hX hH
  have hpoly : (30000*25601344 : ℝ)*(m : ℝ) ≤ (2 : ℝ)^m := by
    have hh : (30000*25601344 : ℝ)*((m : ℝ)+1) ≤ (2 : ℝ)^m := by
      exact_mod_cast (by simpa only [one_mul,pow_one] using hm)
    nlinarith only [hh]
  have hlog : Real.log (X : ℝ) ≤ 25601344*(m : ℝ) := by
    have hh := successor_supply_log_upper m X hX
    have hl2 : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hmul := mul_le_mul_of_nonneg_left hl2 (show (0 : ℝ) ≤ 64*400021*m by positivity)
    nlinarith only [hh,hmul]
  have herr := mul_le_mul hlog (productSupplyTailError_le m) (productSupplyTailError_nonneg m)
    (show (0 : ℝ) ≤ 25601344*m by positivity)
  have hscaled := mul_le_mul_of_nonneg_right hpoly (show (0 : ℝ) ≤ 2^(6400960*m) by positivity)
  have hpow : (2 : ℝ)^m*(2 : ℝ)^(6400960*m) ≤ (H : ℝ) := by
    rw [← pow_add]
    apply le_trans _ (Nat.cast_le.mpr hH)
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith only [herr,hscaled,hpow]


end Erdos821.AnalyticSieve
