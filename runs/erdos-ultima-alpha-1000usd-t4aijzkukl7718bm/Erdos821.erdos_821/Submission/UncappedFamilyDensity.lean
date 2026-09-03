import Submission.UncappedCofactorSieve
import Submission.FixedMassBlockDensity

/-!
# Fixed-mass blockwise density without the endpoint cap

The explicit prime-distribution hypothesis is still required. Removing
the old coefficient cap does not prove distribution at larger moduli.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma eventually_ambient_endpoint_all (r t b h : ℕ) (heq : r+b+h=t) (hb : 2 ≤ b) :
    ∀ᶠ m : ℕ in atTop, ∀ j ∈ range h,
      EndpointPairUpTo (independentN t m) (independentJ (blockCutoff b h j) m) := by
  filter_upwards [eventually_endpoint_pair_ambient t (by omega)] with m hm
  intro j hj
  have hc := blockCutoff_properties r t b h j heq (mem_range.mp hj)
  apply hm _ ?_ _ le_rfl
  exact Nat.le_mul_of_pos_left m (by omega : 0<blockCutoff b h j-1)

lemma family_block_rough_count_le_ambient (M : Finset ℕ) (r q t b c h m : ℕ)
    (hr : r+b+h=t) (hq : q+c+h=t) (_hc : 2 ≤ c) (hh : 1 ≤ h)
    (hM : ∀ d ∈ M, 0 < d ∧ independentN r m ≤ d ∧ d ≤ independentN q m ∧
      d ∈ Nat.smoothNumbers (independentN b m) ∧ Odd d)
    (hend : ∀ j ∈ range h, EndpointPairUpTo (independentN t m) (independentJ (blockCutoff c h j) m))
    (hmass : ∀ j ∈ range h,
      (∑ k ∈ cofactorBlock j m with Even k, 1/(k.totient : ℝ)) ≤
        (4/3 : ℝ)*(1+64*(m : ℝ)*Real.log 2)) :
    (∑ d ∈ M, ((roughProgressionPrimes d (independentN b m) (independentN t m)).card : ℝ)) ≤
      blockSieveMain t c h m*poolTotientMass M+familyBlockError M c h m := by
  have hpairs (d : ℕ) (hd : d ∈ M) :
      ((roughProgressionPrimes d (independentN b m) (independentN t m)).card : ℝ) ≤
        ∑ j ∈ range h, ∑ k ∈ cofactorBlock j m,
          (primePairCofactorCount (independentN t m) (d*k) : ℝ) := by
    have hX : independentN t m ≤ d*2^(64*h*m)*independentN b m := by
      calc
        _ = independentN r m*2^(64*h*m)*independentN b m := by
          simp only [independentN,← pow_add]
          congr 1
          nlinarith only [congrArg (fun z : ℕ => 64*z*m) hr]
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hM d hd).2.1)
    have hp : ((roughProgressionPrimes d (independentN b m) (independentN t m)).card : ℝ) ≤
        ∑ k ∈ Icc 1 (2^(64*h*m)), (primePairCofactorCount (independentN t m) (d*k) : ℝ) := by
      exact_mod_cast rough_composite_progression_card_le_pairs (independentN t m)
        (2^(64*h*m)) (independentN b m) d (hM d hd).1 (hM d hd).2.2.2.1 hX
    rw [sum_cofactorBlock_partition]
    have hset : Ioc 0 (cofactorBlockEndpoint h m)=Icc 1 (2^(64*h*m)) := by
      ext k
      simp only [cofactorBlockEndpoint,if_neg (by omega : h ≠ 0),mem_Ioc,mem_Icc]
      omega
    rw [hset]
    exact hp
  have hblocks (j : ℕ) (hj : j ∈ range h) :
      (∑ d ∈ M, ∑ k ∈ cofactorBlock j m,
        (primePairCofactorCount (independentN t m) (d*k) : ℝ)) ≤
      blockUnitMain t (blockCutoff c h j) m*poolTotientMass M+
        (M.card : ℝ)*(2 : ℝ)^(64*(j+1)*m)*
          ((2 : ℝ)^(64*independentJ (blockCutoff c h j) m)+
            (2 : ℝ)^(16*independentJ (blockCutoff c h j) m)+1) := by
    have hjh := mem_range.mp hj
    have hcut := blockCutoff_properties q t c h j hq hjh
    have hQX : independentN q m*2^(64*(j+1)*m) ≤ independentN t m := by
      simp only [independentN,← pow_add]
      apply Nat.pow_le_pow_right (by decide)
      nlinarith only [congrArg (fun z : ℕ => 64*z*m) hcut.2,Nat.zero_le (blockCutoff c h j*m)]
    exact sum_prime_pair_family_block_ambient M (independentN t m)
      (independentJ (blockCutoff c h j) m) (independentN q m) j m
      (fun d hd => ⟨(hM d hd).1,(hM d hd).2.2.2.2,(hM d hd).2.2.1⟩)
      hQX (hend j hj) (hmass j hj)
  calc
    _ ≤ ∑ d ∈ M, ∑ j ∈ range h, ∑ k ∈ cofactorBlock j m,
        (primePairCofactorCount (independentN t m) (d*k) : ℝ) := sum_le_sum hpairs
    _ = ∑ j ∈ range h, ∑ d ∈ M, ∑ k ∈ cofactorBlock j m,
        (primePairCofactorCount (independentN t m) (d*k) : ℝ) := sum_comm
    _ ≤ ∑ j ∈ range h, (blockUnitMain t (blockCutoff c h j) m*poolTotientMass M+
        (M.card : ℝ)*(2 : ℝ)^(64*(j+1)*m)*
          ((2 : ℝ)^(64*independentJ (blockCutoff c h j) m)+
            (2 : ℝ)^(16*independentJ (blockCutoff c h j) m)+1)) := sum_le_sum hblocks
    _ = _ := by simp only [sum_add_distrib,← sum_mul,mul_assoc,← mul_sum,blockSieveMain,familyBlockError]


theorem fixed_mass_block_smooth_count_ambient (M : ℕ → Finset ℕ) (r q t b c h I W : ℕ)
    (hr : r+b+h=t) (hq : q+c+h=t) (hc : 2 ≤ c) (hh : 1 ≤ h)
    (hIpos : 0 < I) (hWpos : 0 < W)
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
    eventually_ambient_endpoint_all q t c h hq hc,eventually_cofactorBlock_mass_all h,
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
  have hrgh := family_block_rough_count_le_ambient (M m) r q t b c h m hr hq hc hh hM hend hbmass
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
