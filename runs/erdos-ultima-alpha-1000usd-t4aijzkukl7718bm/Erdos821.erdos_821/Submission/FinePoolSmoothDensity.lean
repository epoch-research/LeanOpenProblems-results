import Submission.FinePoolRoughBound

/-!
# Smooth-predecessor prime supply from the thirty-six-band retained-pool sieve

The fixed smoothness ratio is 15600000/40000020. The construction uses a
bounded enlargement to select an actual Mangoldt cutoff with slope near
one, and all estimates are uniform over that enlargement.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 5000000

theorem exists_fine_pool_smooth_prime_count_enlarged :
    ∃ K C : ℕ, 2 ≤ K ∧ 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      (independentN 40000020 m : ℝ) ≤ (C : ℝ)*((m : ℝ)+1)*
        ((smoothPrimePool (K*independentN 40000020 m) (independentN 15600000 m)).card : ℝ) := by
  let W := widePairMassDenom 10000000
  have hW : 0 < W := widePairMassDenom_pos 10000000
  obtain ⟨K,hK,HK⟩ := exists_bounded_gap_mangoldt_unit (99999/100000) (by norm_num)
  let C := 10000*W*16*(K+64*40000020)
  refine ⟨K,C,hK,by dsimp [C]; positivity,?_⟩
  filter_upwards [eventually_fine_pool_rough_rejection_bound,
    eventually_uniform_widePair_error 10000000 K (10000*W) (by decide) (by positivity),
    eventually_uniform_block_total_error (widePairPool 10000000) 20000004 40000020 20000016 0 K 16 (10000*W)
      (by decide) (by decide) (by omega) (by positivity) (widePairPool_card_le 10000000),
    eventually_ge_atTop (max 1 K)] with m hrough0 herr0 hpower0 hm
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hm
  have hmK : K ≤ m := (le_max_right _ _).trans hm
  let N₀ := independentN 40000020 m
  let Y := independentN 15600000 m
  let M := widePairPool 10000000 m
  let V := poolTotientMass M
  have hN₀ : 1 ≤ N₀ := by dsimp [N₀,independentN]; exact Nat.one_le_pow _ _ (by decide)
  obtain ⟨N,hN,hnψ⟩ := HK N₀ hN₀
  obtain ⟨hlo,hhi⟩ := mem_Icc.mp hN
  have hN1 : 1 ≤ N := hN₀.trans hlo
  have hV : 0 ≤ V := poolTotientMass_nonneg M
  have hmass : 1/(W : ℝ) ≤ V := widePairPool_mass_lower 10000000 m hm1
  have hNu : N ≤ independentN 40000021 m :=
    hhi.trans (fixed_multiple_le_next_exponent 40000020 K m hmK)
  have hM (d : ℕ) (hd : d ∈ M) :
      0 < d ∧ independentN 20000000 m ≤ d ∧ d ≤ independentN 20000004 m ∧ d ∈ Nat.smoothNumbers Y := by
    have hh := widePairPool_bounds 10000000 m d hd
    exact ⟨by omega,hh.2.1,hh.2.2,(widePairPool_smooth_odd 10000000 15600000 m d
      (by decide) (by decide) hm1 hd).1⟩
  have hI (n : ℕ) (hn : 0<n) (hnN : n<N) : (M.filter (fun d => d ∣ n)).card ≤ 16 :=
    widePair_divisor_incidence_le_enlarged 10000000 m n (by decide) hm1 hn (hnN.trans_le hNu)
  have hscale : (N₀ : ℝ)/(10000*W : ℕ) ≤ (N : ℝ)/10000*V := by
    calc
      _ = (N₀ : ℝ)/10000*(1/(W : ℝ)) := by push_cast; ring
      _ ≤ (N : ℝ)/10000*(1/(W : ℝ)) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  have herr : (∑ d ∈ M, compositeProgressionError d N) ≤ (N : ℝ)/10000*V :=
    (herr0 N hhi).trans hscale
  have hpower : Real.log (N : ℝ)*(2*(16 : ℝ)*Real.sqrt N) ≤ (N : ℝ)/10000*V := by
    have hh := (hpower0 N hhi).trans hscale
    simpa only [familyBlockError,range_zero,sum_empty,mul_zero,zero_add] using hh
  have hw : (99989/100000 : ℝ)*(N : ℝ)*V ≤ ∑ d ∈ M, residueOneMangoldt d N := by
    have hp := composite_progression_total_lower M (fun d hd => (hM d hd).1) N
    have hh := mul_le_mul_of_nonneg_right hnψ.le hV
    change mangoldtSum N*V-(∑ d ∈ M, compositeProgressionError d N) ≤ _ at hp
    simp only [div_eq_mul_inv] at hp hh herr ⊢
    nlinarith only [hp,hh,herr]
  have hrough : Real.log (N : ℝ)*(∑ d ∈ M, ((roughProgressionPrimes d Y N).card : ℝ)) ≤
      (1999/2000 : ℝ)*(N : ℝ)*V := hrough0 N hlo hNu
  have hupper := family_progression_weight_le_smooth_count M N Y 16 hN1 hI
  have hretain : (N : ℝ)/10000*V ≤ (16 : ℝ)*Real.log N*((smoothPrimePool N Y).card : ℝ) := by
    have hNV : 0 ≤ (N : ℝ)*V := mul_nonneg (Nat.cast_nonneg _) hV
    simp only [div_eq_mul_inv,Nat.cast_ofNat] at hw hupper hrough hpower ⊢
    nlinarith only [hw,hupper,hrough,hpower,hNV]
  have hloCount : (N₀ : ℝ)/(10000*W : ℕ) ≤
      (16 : ℝ)*Real.log N*((smoothPrimePool N Y).card : ℝ) := hscale.trans hretain
  have hlog := log_fixed_cutoff_upper 40000020 K m N (by omega) hhi
  have hcCount : ((smoothPrimePool N Y).card : ℝ) ≤
      (smoothPrimePool (K*N₀) Y).card := by
    apply Nat.cast_le.mpr
    apply card_le_card
    intro p hp
    obtain ⟨hp,hps⟩ := mem_filter.mp hp
    obtain ⟨hpN,hpr⟩ := Nat.mem_primesBelow.mp hp
    exact mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega,hpr⟩,hps⟩
  have hlogCount := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ)≤16)) (Nat.cast_nonneg (smoothPrimePool N Y).card)
  have hh := hloCount.trans (hlogCount.trans (mul_le_mul_of_nonneg_left hcCount (by positivity)))
  have hden : (0 : ℝ)<(10000*W : ℕ) := by exact_mod_cast (show 0<10000*W by positivity)
  have hf := (div_le_iff₀ hden).mp hh
  change (N₀ : ℝ) ≤ (C : ℝ)*((m : ℝ)+1)*((smoothPrimePool (K*N₀) Y).card : ℝ)
  convert hf using 1
  dsimp [C]
  push_cast
  ring

theorem exists_fine_pool_smooth_prime_count :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      (independentN 40000020 m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN 40000020 m) (independentN 15600000 m)).card : ℝ) := by
  obtain ⟨K,C,_hK,hC,HC⟩ := exists_fine_pool_smooth_prime_count_enlarged
  exact eventual_single_log_count_of_fixed_enlargement 40000020 15600000 K C (by decide) hC HC

end Erdos821
