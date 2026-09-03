import Submission.UnitSlopeWideDensity
import Submission.FiniteLocalBlockSieve

/-!
# Unit-slope smooth-prime density with a fixed finite local correction

Every prime in the retained pool is eventually excluded from the rough
moduli. The finite cutoff is fixed before the scale tends to infinity.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 4000000

lemma widePairPool_avoids_retained (D a m d : ℕ) (ha : 1 ≤ a) (hDm : D ≤ m)
    (hd : d ∈ widePairPool a m) : ∀ p ∈ Sieve.retainedPrimePool D, ¬p ∣ d := by
  intro p hp hpd
  obtain ⟨hpr,hp2,hpD⟩ := Sieve.retainedPrimePool_properties D p hp
  have hd0 : d ≠ 0 := by have := (widePairPool_bounds a m d hd).1; omega
  have hh := widePairPool_rough a m d hd p (mem_erase.mpr ⟨by omega,Nat.mem_divisors.mpr ⟨hpd,hd0⟩⟩)
  have hmN : m < independentN a m := by
    apply (Nat.lt_two_pow_self (n := m)).trans_le
    apply Nat.pow_le_pow_right (by decide)
    have ham := Nat.le_mul_of_pos_left m ha
    nlinarith only [ham,Nat.zero_le m]
  omega

lemma eventually_uniform_finite_endpoint (D q t c h K : ℕ) (heq : q+c+h=t) (hc : 2 ≤ c) :
    ∀ᶠ m : ℕ in atTop, ∀ X : ℕ, X ≤ K*independentN t m →
      ∀ j ∈ range h, FiniteEndpointPairUpTo (Sieve.retainedPrimePool D) X (independentJ (blockCutoff c h j) m) := by
  filter_upwards [eventually_finite_endpoint_pair_ambient (Sieve.retainedPrimePool D)
    (fun p hp => ⟨(Sieve.retainedPrimePool_properties D p hp).1,(Sieve.retainedPrimePool_properties D p hp).2.1⟩) (t+1) (by omega),
    eventually_ge_atTop K] with m hm hmK
  intro X hX j hj
  have hcut := blockCutoff_properties q t c h j heq (mem_range.mp hj)
  apply hm _ ?_ X (hX.trans (fixed_multiple_le_next_exponent t K m hmK))
  exact Nat.le_mul_of_pos_left m (by omega : 0 < blockCutoff c h j-1)

/-- The resulting prime supply is eventually available, not just cofinally. -/
theorem widePair_finite_unit_slope_smooth_count (D a b c h : ℕ) (hDcut : 2 ≤ D) (ha : 22 ≤ a)
    (hb : a+3 ≤ b) (hbc : c+5=b) (heq : 2*a+b+h=widePairScale a+1)
    (hc : 3 ≤ c) (hh : 1 ≤ h)
    (hcoef : finiteBlockMainLimit D (widePairScale a) c h < 1) :
    ∃ K C : ℕ, 2 ≤ K ∧ 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      (independentN (widePairScale a) m : ℝ) ≤ (C : ℝ)*((m : ℝ)+1)*
        ((smoothPrimePool (K*independentN (widePairScale a) m) (independentN b m)).card : ℝ) := by
  let t := widePairScale a
  let W := widePairMassDenom a
  let α := finiteBlockMainLimit D t c h
  have hα0 : 0 ≤ α := finiteBlockMainLimit_nonneg _ _ _ _ hDcut
  have hα1 : α < 1 := hcoef
  have ht : 1 ≤ t := by dsimp [t,widePairScale]; omega
  have hq : (2*a+4)+c+h=t := by dsimp [t]; omega
  have hW : 0 < W := widePairMassDenom_pos a
  obtain ⟨E,hD⟩ := exists_nat_gt (max 1 (4/(1-α)))
  have hDR : (0 : ℝ) < E := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hD)
  have hDn : 0 < E := by exact_mod_cast hDR
  have hgap : 4/(E : ℝ) < 1-α := by
    have hh := (div_lt_iff₀ (sub_pos.mpr hα1)).mp ((le_max_right _ _).trans_lt hD)
    apply (div_lt_iff₀ hDR).mpr
    linarith only [hh]
  obtain ⟨K,hK,HK⟩ := exists_bounded_gap_mangoldt_unit (α+4/(E : ℝ)) (by linarith only [hgap])
  let C := E*W*16*(K+64*t)
  refine ⟨K,C,hK,by dsimp [C]; positivity,?_⟩
  have hmain : α < α+1/(E : ℝ) := lt_add_of_pos_right _ (by positivity)
  filter_upwards [eventually_uniform_widePair_error a K (E*W) (by omega) (Nat.mul_pos hDn hW),
    eventually_uniform_block_total_error (widePairPool a) (2*a+4) t c h K 16 (E*W)
      hq (by omega) (by omega) (Nat.mul_pos hDn hW) (widePairPool_card_le a),
    eventually_uniform_finite_block_main D (2*a+4) t c h K hDcut hq (by omega) (by omega)
      (α+1/(E : ℝ)) hmain,
    eventually_uniform_finite_endpoint D (2*a+4) t c h K hq (by omega),
    eventually_cofactorBlock_finite_mass_all D h hDcut,eventually_ge_atTop (max 1 K),eventually_ge_atTop D]
    with m herr0 hother0 hmain0 hend0 hmass0 hm hmD
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hm
  have hKm : K ≤ m := (le_max_right _ _).trans hm
  let N₀ := independentN t m
  let Y := independentN b m
  let M := widePairPool a m
  let V := poolTotientMass M
  have hN₀ : 1 ≤ N₀ := by dsimp [N₀,independentN]; exact Nat.one_le_pow _ _ (by decide)
  obtain ⟨N,hN,hnψ⟩ := HK N₀ hN₀
  obtain ⟨hlo,hhi⟩ := mem_Icc.mp hN
  have hN1 : 1 ≤ N := hN₀.trans hlo
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hV : 0 ≤ V := poolTotientMass_nonneg M
  have hmass : 1/(W : ℝ) ≤ V := widePairPool_mass_lower a m hm1
  have hM (d : ℕ) (hd : d ∈ M) :
      0 < d ∧ independentN (2*a) m ≤ d ∧ d ≤ independentN (2*a+4) m ∧
        d ∈ Nat.smoothNumbers Y ∧ Odd d := by
    have hh := widePairPool_bounds a m d hd
    exact ⟨by omega,hh.2.1,hh.2.2,widePairPool_smooth_odd a b m d (by omega) hb hm1 hd⟩
  have hI (n : ℕ) (hn : 0<n) (hnN : n<N) : (M.filter (fun d => d ∣ n)).card ≤ 16 :=
    widePair_divisor_incidence_le_enlarged a m n ha hm1 hn
      (hnN.trans_le (hhi.trans (fixed_multiple_le_next_exponent t K m hKm)))
  have hscale : (N₀ : ℝ)/(E*W : ℕ) ≤ (N : ℝ)/(E : ℝ)*V := by
    calc
      _ = (N₀ : ℝ)/(E : ℝ)*(1/(W : ℝ)) := by push_cast; ring
      _ ≤ (N : ℝ)/(E : ℝ)*(1/(W : ℝ)) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  have herr : (∑ d ∈ M, compositeProgressionError d N) ≤ (N : ℝ)/(E : ℝ)*V :=
    (herr0 N hhi).trans hscale
  have hother : Real.log (N : ℝ)*(familyBlockError M c h m+2*(16 : ℝ)*Real.sqrt N) ≤
      (N : ℝ)/(E : ℝ)*V := (hother0 N hhi).trans hscale
  have hw : (α+3/(E : ℝ))*(N : ℝ)*V ≤ ∑ d ∈ M, residueOneMangoldt d N := by
    have hp := composite_progression_total_lower M (fun d hd => (hM d hd).1) N
    have hh := mul_le_mul_of_nonneg_right hnψ.le hV
    change mangoldtSum N*V-(∑ d ∈ M, compositeProgressionError d N) ≤ _ at hp
    simp only [div_eq_mul_inv] at hp hh herr ⊢
    nlinarith only [hp,hh,herr]
  have hcoverage : N ≤ independentN (2*a+b+h) m := by
    rw [heq]
    exact hhi.trans (fixed_multiple_le_next_exponent t K m hKm)
  have hrough := family_block_rough_count_le_ambient_finite_cutoff M D (2*a) (2*a+4)
    t b c h m N hcoverage hlo hq (by omega) hh hM
    (fun d hd => widePairPool_avoids_retained D a m d (by omega) hmD hd) (hend0 N hhi) hmass0
  have hupper := family_progression_weight_le_smooth_count M N Y 16 hN1 hI
  have hmainN := mul_le_mul_of_nonneg_right (hmain0 N hlo hhi) hV
  have hroughN := mul_le_mul_of_nonneg_left hrough (Real.log_natCast_nonneg N)
  have hretain : (N : ℝ)/(E : ℝ)*V ≤
      (16 : ℝ)*Real.log N*((smoothPrimePool N Y).card : ℝ) := by
    change Real.log (N : ℝ)*(∑ d ∈ M, ((roughProgressionPrimes d Y N).card : ℝ)) ≤
      Real.log (N : ℝ)*(finiteBlockSieveMainAt D N c h m*V+familyBlockError M c h m) at hroughN
    simp only [div_eq_mul_inv,Nat.cast_ofNat] at hw hupper hmainN hroughN hother ⊢
    nlinarith only [hw,hupper,hmainN,hroughN,hother]
  have hloCount : (N₀ : ℝ)/(E*W : ℕ) ≤
      (16 : ℝ)*Real.log N*((smoothPrimePool N Y).card : ℝ) := hscale.trans hretain
  have hlog := log_fixed_cutoff_upper t K m N (by omega) hhi
  have hcCount : ((smoothPrimePool N Y).card : ℝ) ≤
      (smoothPrimePool (K*N₀) Y).card := by
    apply Nat.cast_le.mpr
    apply card_le_card
    intro p hp
    obtain ⟨hp,hps⟩ := mem_filter.mp hp
    obtain ⟨hpN,hpr⟩ := Nat.mem_primesBelow.mp hp
    exact mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega,hpr⟩,hps⟩
  have hlogCount := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 16))
    (Nat.cast_nonneg (smoothPrimePool N Y).card)
  have hh := hloCount.trans (hlogCount.trans
    (mul_le_mul_of_nonneg_left hcCount (by positivity)))
  have hDW : (0 : ℝ) < (E*W : ℕ) := by exact_mod_cast Nat.mul_pos hDn hW
  have hf := (div_le_iff₀ hDW).mp hh
  change (N₀ : ℝ) ≤ (C : ℝ)*((m : ℝ)+1)*((smoothPrimePool (K*N₀) Y).card : ℝ)
  convert hf using 1
  dsimp [C]
  push_cast
  ring

end Erdos821
