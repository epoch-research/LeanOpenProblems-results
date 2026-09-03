import Submission.BlockCofactorSieve
import Submission.FlexibleChebyshevGain

/-!
# Structured sieve estimates with block-dependent lengths

The block index is fixed before the scale tends to infinity. This module
combines the direct interval bounds without subtracting prefix estimates.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

def blockCutoff (b h j : ℕ) : ℕ := b+h-j-1

lemma blockCutoff_properties (r t b h j : ℕ) (heq : r+b+h=t) (hj : j<h) :
    b ≤ blockCutoff b h j ∧ r+blockCutoff b h j+(j+1)=t := by
  dsimp [blockCutoff]
  omega

noncomputable def blockUnitMain (t c m : ℕ) : ℝ :=
  (2/675 : ℝ)*(independentN t m : ℝ)*(1+64*(m : ℝ)*Real.log 2)/
    ((independentJ c m : ℝ)*Real.log 2)^2

noncomputable def blockSieveMain (t b h m : ℕ) : ℝ :=
  ∑ j ∈ range h, blockUnitMain t (blockCutoff b h j) m

noncomputable def blockSieveError (r b h m : ℕ) : ℝ :=
  ∑ j ∈ range h, independentSieveError r (blockCutoff b h j) (j+1) m

noncomputable def blockMainLimit (t b h : ℕ) : ℝ :=
  ∑ j ∈ range h, independentMainLimit t (blockCutoff b h j) 1

noncomputable def blockMainRemainder (t b h : ℕ) : ℝ :=
  ∑ j ∈ range h, independentMainRemainder t (blockCutoff b h j)

lemma block_unit_main_normalized (t c m : ℕ) (hc : 2 ≤ c) (hm : 1 ≤ m) :
    Real.log (independentN t m : ℝ)*blockUnitMain t c m =
      (independentMainLimit t c 1+independentMainRemainder t c/(m : ℝ))*
        (independentN t m : ℝ) := by
  have hcR : (0 : ℝ) < (c : ℝ)-1 := by
    have : (2 : ℝ) ≤ c := by exact_mod_cast hc
    linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log (independentN t m : ℝ) = 64*(t : ℝ)*m*Real.log 2 := by
    simp only [independentN,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_mul]
  rw [hlog]
  simp only [blockUnitMain,independentMainLimit,independentMainRemainder,
    independentJ,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ c),Nat.cast_one]
  field_simp
  ring

lemma block_sieve_main_normalized (r t b h m : ℕ) (heq : r+b+h=t)
    (hb : 2 ≤ b) (hm : 1 ≤ m) :
    Real.log (independentN t m : ℝ)*blockSieveMain t b h m =
      (blockMainLimit t b h+blockMainRemainder t b h/(m : ℝ))*(independentN t m : ℝ) := by
  unfold blockSieveMain blockMainLimit blockMainRemainder
  rw [mul_sum]
  calc
    _ = ∑ j ∈ range h, (independentMainLimit t (blockCutoff b h j) 1+
        independentMainRemainder t (blockCutoff b h j)/(m : ℝ))*(independentN t m : ℝ) := by
      apply sum_congr rfl
      intro j hj
      exact block_unit_main_normalized t _ m
        (hb.trans (blockCutoff_properties r t b h j heq (mem_range.mp hj)).1) hm
    _ = _ := by rw [← sum_mul,sum_add_distrib,← sum_div]

lemma eventually_block_sieve_main_constant (r t b h : ℕ) (heq : r+b+h=t)
    (hb : 2 ≤ b) (a : ℝ) (ha : blockMainLimit t b h<a) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (independentN t m : ℝ)*blockSieveMain t b h m ≤ a*(independentN t m : ℝ) := by
  have hlim : Tendsto (fun m : ℕ => blockMainLimit t b h+
      blockMainRemainder t b h/(m : ℝ)) atTop (𝓝 (blockMainLimit t b h)) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [hlim.eventually (eventually_le_nhds ha),eventually_ge_atTop 1] with m ha hm
  rw [block_sieve_main_normalized r t b h m heq hb hm]
  exact mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _)

lemma eventually_block_endpoint_all (r t b h : ℕ) (heq : r+b+h=t) (hb : 2 ≤ b) :
    ∀ᶠ m : ℕ in atTop, ∀ j ∈ range h,
      EndpointPairAt (independentJ (blockCutoff b h j) m) := by
  rw [eventually_all_finset]
  intro j hj
  exact eventually_independent_endpoint _
    (hb.trans (blockCutoff_properties r t b h j heq (mem_range.mp hj)).1)

lemma block_rough_count_le (r t b h m : ℕ) (heq : r+b+h=t)
    (hb : 2 ≤ b) (hh : 1 ≤ h) (hcap : t+5 ≤ 5*b) (hm : max 2 r ≤ m)
    (hend : ∀ j ∈ range h, EndpointPairAt (independentJ (blockCutoff b h j) m))
    (hmass : ∀ j ∈ range h,
      (∑ k ∈ cofactorBlock j m with Even k, 1/(k.totient : ℝ)) ≤
        (4/3 : ℝ)*(1+64*(m : ℝ)*Real.log 2)) :
    (∑ d ∈ primeProductModuli r m,
      ((roughProgressionPrimes d (independentN b m) (independentN t m)).card : ℝ)) ≤
        blockSieveMain t b h m*primeProductReciprocalMass r m+blockSieveError r b h m := by
  let M := primeProductModuli r m
  let Q := 2^(64*r*(m+1))
  have hM (d : ℕ) (hd : d ∈ M) :
      0 < d ∧ Odd d ∧ d ≤ Q := by
    have hp := primeProductModuli_properties hd
    refine ⟨hp.1,primeProductModuli_odd (by omega) hd,?_⟩
    have hQ : progressionScaleN (m+1)^r = Q := by
      dsimp [Q,progressionScaleN]
      rw [← pow_mul]
      congr 1
      ring
    exact hQ ▸ hp.2.2.2.2
  have hD (d : ℕ) (hd : d ∈ M) : 2^(64*r*m) ≤ d := by
    have h := (primeProductModuli_properties hd).2.2.2.1
    have hpow : progressionScaleN m^r=2^(64*r*m) := by
      simp only [progressionScaleN,← pow_mul]
      congr 1
      ring
    simpa only [hpow] using h
  have hY (d : ℕ) (hd : d ∈ M) : d ∈ Nat.smoothNumbers (independentN b m) := by
    apply Nat.smoothNumbers_mono ?_ (primeProductModuli_smooth (by omega) hd)
    apply Nat.pow_le_pow_right (by decide)
    change 128*m ≤ 64*b*m
    nlinarith only [Nat.mul_le_mul_right m hb]
  have hpairs (d : ℕ) (hd : d ∈ M) :
      ((roughProgressionPrimes d (independentN b m) (independentN t m)).card : ℝ) ≤
        ∑ j ∈ range h, ∑ k ∈ cofactorBlock j m,
          (primePairCofactorCount (independentN t m) (d*k) : ℝ) := by
    have hX : independentN t m ≤ d*2^(64*h*m)*independentN b m := by
      calc
        _ = 2^(64*r*m)*2^(64*h*m)*independentN b m := by
          simp only [independentN,← pow_add]
          congr 1
          nlinarith only [congrArg (fun z : ℕ => 64*z*m) heq]
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hD d hd))
    have hp : ((roughProgressionPrimes d (independentN b m) (independentN t m)).card : ℝ) ≤
        ∑ k ∈ Icc 1 (2^(64*h*m)), (primePairCofactorCount (independentN t m) (d*k) : ℝ) := by
      exact_mod_cast rough_composite_progression_card_le_pairs (independentN t m)
        (2^(64*h*m)) (independentN b m) d (hM d hd).1 (hY d hd) hX
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
      blockUnitMain t (blockCutoff b h j) m*primeProductReciprocalMass r m+
        independentSieveError r (blockCutoff b h j) (j+1) m := by
    have hc := blockCutoff_properties r t b h j heq (mem_range.mp hj)
    have hbc : 2 ≤ blockCutoff b h j := hb.trans hc.1
    have hcapc : t+5 ≤ 5*blockCutoff b h j := hcap.trans (Nat.mul_le_mul_left 5 hc.1)
    have hQX : Q*2^(64*(j+1)*m) ≤ independentN t m := by
      dsimp only [Q,independentN]
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by decide)
      have hrm : r ≤ blockCutoff b h j*m := (by omega : r ≤ m).trans
        (Nat.le_mul_of_pos_left m (by omega))
      nlinarith only [hrm,congrArg (fun z : ℕ => 64*z*m) hc.2]
    have hhcap := independent_coefficient_cap r t (blockCutoff b h j) (j+1) m
      hc.2 hbc hcapc (by omega)
    exact sum_prime_pair_family_block_endpoint M (independentN t m)
      (independentJ (blockCutoff b h j) m) Q j m hM hQX hhcap (hend j hj) (hmass j hj)
  calc
    _ ≤ ∑ d ∈ M, ∑ j ∈ range h, ∑ k ∈ cofactorBlock j m,
        (primePairCofactorCount (independentN t m) (d*k) : ℝ) := sum_le_sum hpairs
    _ = ∑ j ∈ range h, ∑ d ∈ M, ∑ k ∈ cofactorBlock j m,
        (primePairCofactorCount (independentN t m) (d*k) : ℝ) := sum_comm
    _ ≤ ∑ j ∈ range h, (blockUnitMain t (blockCutoff b h j) m*primeProductReciprocalMass r m+
        independentSieveError r (blockCutoff b h j) (j+1) m) := sum_le_sum hblocks
    _ = _ := by rw [sum_add_distrib,← sum_mul]; rfl

end Erdos821
