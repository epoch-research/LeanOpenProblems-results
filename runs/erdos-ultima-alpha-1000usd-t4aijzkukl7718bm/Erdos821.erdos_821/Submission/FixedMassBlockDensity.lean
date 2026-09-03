import Submission.FamilyBlockSieve

/-!
# Single-logarithm prime counts from fixed-mass blockwise families

The arithmetic distribution hypothesis is separate from the finite sieve
estimate; later applications must prove it for their particular family.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma fixed_mass_progression_lower (M : ℕ → Finset ℕ) (t W E s : ℕ)
    (ht : 1 ≤ t) (hW : 0 < W)
    (hpos : ∀ᶠ m : ℕ in atTop, ∀ d ∈ M m, 0 < d)
    (hmass : ∀ᶠ m : ℕ in atTop, 1/(W : ℝ) ≤ poolTotientMass (M m))
    (herror : ∀ᶠ m : ℕ in atTop,
      (∑ d ∈ M m, compositeProgressionError d (independentN t m)) ≤
        (E : ℝ)*((m : ℝ)+1)^s*(2 : ℝ)^((64*t-1)*m))
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < chebyshevRatioConstant) :
    ∀ᶠ m : ℕ in atTop,
      c*(independentN t m : ℝ)*poolTotientMass (M m) ≤
        ∑ d ∈ M m, residueOneMangoldt d (independentN t m) := by
  let a := (c+chebyshevRatioConstant)/2
  have hca : c<a := by dsimp [a]; linarith
  have hac : a<chebyshevRatioConstant := by dsimp [a]; linarith
  obtain ⟨D,hD⟩ := exists_nat_gt (max 1 (1/(a-c)))
  have hDpos : (0 : ℝ)<D := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hD)
  have hDn : 0<D := by exact_mod_cast hDpos
  have hmargin : 1/(D : ℝ)<a-c := by
    apply (div_lt_iff₀ hDpos).mpr
    have h := (div_lt_iff₀ (sub_pos.mpr hca)).mp ((le_max_right _ _).trans_lt hD)
    linarith only [h]
  filter_upwards [hpos,hmass,herror,
    eventually_power_saving_le_divisor t E s (D*W) ht (Nat.mul_pos hDn hW),
    eventually_progression_mangoldt_lower_constant t ht a (hc0.trans hca.le) hac]
      with m hp hm he hes hpsi
  have hmass0 : 0 ≤ poolTotientMass (M m) := poolTotientMass_nonneg _
  have herr : (∑ d ∈ M m, compositeProgressionError d (independentN t m)) ≤
      (independentN t m : ℝ)/(D : ℝ)*poolTotientMass (M m) := by
    apply he.trans (hes.trans ?_)
    calc
      _ = (independentN t m : ℝ)/(D : ℝ)*(1/(W : ℝ)) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
  have hpsi' : a*(independentN t m : ℝ) ≤ mangoldtSum (independentN t m) := by
    simpa only [independentN,progressionScaleN,mul_assoc] using hpsi
  have hmain := mul_le_mul_of_nonneg_right hpsi' hmass0
  have htotal := composite_progression_total_lower (M m) hp (independentN t m)
  have hmargin' := mul_le_mul_of_nonneg_right hmargin.le
    (show 0 ≤ (independentN t m : ℝ)*poolTotientMass (M m) by positivity)
  change a*(independentN t m : ℝ)*poolTotientMass (M m) ≤ _ at hmain
  change mangoldtSum (independentN t m)*poolTotientMass (M m)-_ ≤ _ at htotal
  simp only [div_eq_mul_inv] at hmain herr htotal hmargin' ⊢
  nlinarith only [hmain,herr,htotal,hmargin']

/-- Positive reciprocal modulus mass removes every logarithmic counting
loss except the one converting Mangoldt weight to a prime count. -/
theorem fixed_mass_block_smooth_count (M : ℕ → Finset ℕ) (r q t b c h I W : ℕ)
    (hr : r+b+h=t) (hq : q+c+h=t) (hc : 2 ≤ c) (hh : 1 ≤ h)
    (hcap : t+4 ≤ 5*c) (hIpos : 0 < I) (hWpos : 0 < W)
    (hM : ∀ᶠ m : ℕ in atTop, ∀ d ∈ M m,
      0 < d ∧ independentN r m ≤ d ∧ d ≤ independentN q m ∧
        d ∈ Nat.smoothNumbers (independentN b m) ∧ Odd d)
    (hmass : ∀ᶠ m : ℕ in atTop, 1/(W : ℝ) ≤ poolTotientMass (M m))
    (hweight : ∀ a : ℝ, 0 ≤ a → a < chebyshevRatioConstant →
      ∀ᶠ m : ℕ in atTop,
        a*(independentN t m : ℝ)*poolTotientMass (M m) ≤
          ∑ d ∈ M m, residueOneMangoldt d (independentN t m))
    (hI : ∀ᶠ m : ℕ in atTop, ∀ n : ℕ, 0 < n → n < independentN t m →
      ((M m).filter (fun d => d ∣ n)).card ≤ I)
    (hcoef : blockMainLimit t c h < chebyshevRatioConstant) :
    ∃ C : ℕ, 0<C ∧ ∀ᶠ m : ℕ in atTop,
      (independentN t m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN t m) (independentN b m)).card : ℝ) := by
  let a := blockMainLimit t c h
  have ha0 : 0 ≤ a := blockMainLimit_nonneg t c h
  obtain ⟨D,hD⟩ := exists_nat_gt (max 1 (3/(chebyshevRatioConstant-a)))
  have hDpos : (0 : ℝ)<D := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hD)
  have hDn : 0<D := by exact_mod_cast hDpos
  have hgap : 3/(D : ℝ)<chebyshevRatioConstant-a := by
    apply (div_lt_iff₀ hDpos).mpr
    have h := (div_lt_iff₀ (sub_pos.mpr hcoef)).mp ((le_max_right _ _).trans_lt hD)
    linarith only [h]
  let C := D*W*I*(64*t)
  have ht : 1 ≤ t := by omega
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  have ha : a<a+1/(D : ℝ) := lt_add_of_pos_right a (by positivity)
  filter_upwards [hM,hmass,hI,hweight (a+3/(D : ℝ)) (by positivity) (by linarith),
    eventually_block_sieve_main_constant q t c h hq hc (a+1/(D : ℝ)) ha,
    eventually_block_endpoint_all q t c h hq hc,eventually_cofactorBlock_mass_all h,
    eventually_power_saving_le_divisor t (64*t*(3*h+2*I)) 1 (D*W) ht (Nat.mul_pos hDn hWpos),
    eventually_ge_atTop 1] with m hM hm hI hw hmain hend hbmass hes hm1
  let N := independentN t m
  let Y := independentN b m
  let S := smoothPrimePool N Y
  let V := poolTotientMass (M m)
  have hV : 0 ≤ V := poolTotientMass_nonneg _
  have hcard : (M m).card ≤ independentN q m := by
    have hsub : M m ⊆ Icc 1 (independentN q m) :=
      fun d hd => mem_Icc.mpr ⟨(hM d hd).1,(hM d hd).2.2.1⟩
    exact (card_le_card hsub).trans_eq (by simp)
  have herr : Real.log (N : ℝ)*(familyBlockError (M m) c h m+2*(I : ℝ)*Real.sqrt N) ≤
      (N : ℝ)/(D : ℝ)*V := by
    apply (family_block_total_error_bound (M m) q t c h m I hq hc hcard).trans
    have hes' : (64*t*(3*h+2*I) : ℕ)*((m : ℝ)+1)*(2 : ℝ)^((64*t-1)*m) ≤
        (N : ℝ)/(D*W : ℕ) := by simpa only [pow_one] using hes
    apply hes'.trans
    calc
      _ = (N : ℝ)/(D : ℝ)*(1/(W : ℝ)) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
  have hrgh := family_block_rough_count_le (M m) r q t b c h m hr hq hc hh hcap hM hend hbmass
  have hupper := family_progression_weight_le_smooth_count (M m) N Y I
    (Nat.one_le_pow _ _ (by decide)) hI
  have hrlog := mul_le_mul_of_nonneg_left hrgh (Real.log_natCast_nonneg N)
  have hmainW := mul_le_mul_of_nonneg_right hmain hV
  have hretain : (N : ℝ)/(D : ℝ)*V ≤ (I : ℝ)*Real.log N*(S.card : ℝ) := by
    change (a+3/(D : ℝ))*(N : ℝ)*V ≤ ∑ d ∈ M m, residueOneMangoldt d N at hw
    change Real.log (N : ℝ)*blockSieveMain t c h m*V ≤
      (a+1/(D : ℝ))*(N : ℝ)*V at hmainW
    change Real.log (N : ℝ)*(∑ d ∈ M m, ((roughProgressionPrimes d Y N).card : ℝ)) ≤
      Real.log (N : ℝ)*(blockSieveMain t c h m*V+_) at hrlog
    change _ ≤ Real.log (N : ℝ)*((I : ℝ)*(S.card : ℝ)+_+_) at hupper
    simp only [div_eq_mul_inv] at hw hupper hrlog hmainW herr ⊢
    nlinarith only [hw,hupper,hrlog,hmainW,herr]
  have hlo : (N : ℝ)/((D : ℝ)*W) ≤ (I : ℝ)*Real.log N*(S.card : ℝ) := by
    apply le_trans _ hretain
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ (N : ℝ)/(D : ℝ) by positivity)
    convert hh using 1
    ring
  have hlog : Real.log (N : ℝ) ≤ 64*(t : ℝ)*m := by
    simpa only [N,independentN,Nat.cast_mul,Nat.cast_ofNat] using log_two_pow_le (64*t*m)
  have hu := hlo.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg I)) (Nat.cast_nonneg S.card))
  have hWreal : (0 : ℝ)<W := by exact_mod_cast hWpos
  have hf := (div_le_iff₀ (mul_pos hDpos hWreal)).mp hu
  change (N : ℝ) ≤ (C : ℝ)*m*(S.card : ℝ)
  convert hf using 1
  dsimp [C]
  push_cast
  ring

end Erdos821
