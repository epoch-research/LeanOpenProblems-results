import Submission.BlockCompositeGain
import Submission.WideIncidences

/-!
# Blockwise sieve bounds for general fixed-mass modulus families

The lower and upper modulus exponents are separate. This permits wide
families with constant reciprocal mass and a single-logarithm prime count.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma eventually_power_saving_le_divisor (t C s D : ℕ) (ht : 1 ≤ t) (hD : 0 < D) :
    ∀ᶠ m : ℕ in atTop,
      (C : ℝ)*((m : ℝ)+1)^s*(2 : ℝ)^((64*t-1)*m) ≤
        (independentN t m : ℝ)/(D : ℝ) := by
  filter_upwards [eventually_nat_poly_le_two_pow 1 (D*C) s] with m hm
  have hp : (D : ℝ)*C*((m : ℝ)+1)^s ≤ (2 : ℝ)^m := by
    exact_mod_cast (show (D*C)*(m+1)^s ≤ 2^m by simpa only [one_mul] using hm)
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  apply (le_div_iff₀ hDpos).mpr
  calc
    _ = ((D : ℝ)*C*((m : ℝ)+1)^s)*(2 : ℝ)^((64*t-1)*m) := by ring
    _ ≤ (2 : ℝ)^m*(2 : ℝ)^((64*t-1)*m) := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by
      simp only [independentN,Nat.cast_pow,Nat.cast_ofNat,← pow_add]
      congr 1
      have he := Nat.sub_add_cancel (by omega : 1 ≤ 64*t)
      nlinarith only [he]

noncomputable def familyBlockError (M : Finset ℕ) (c h m : ℕ) : ℝ :=
  (M.card : ℝ)*∑ j ∈ range h, (2 : ℝ)^(64*(j+1)*m)*
    ((2 : ℝ)^(64*independentJ (blockCutoff c h j) m)+
      (2 : ℝ)^(16*independentJ (blockCutoff c h j) m)+1)

lemma family_block_rough_count_le (M : Finset ℕ) (r q t b c h m : ℕ)
    (hr : r+b+h=t) (hq : q+c+h=t) (_hc : 2 ≤ c) (hh : 1 ≤ h)
    (hcap : t+4 ≤ 5*c)
    (hM : ∀ d ∈ M, 0 < d ∧ independentN r m ≤ d ∧ d ≤ independentN q m ∧
      d ∈ Nat.smoothNumbers (independentN b m) ∧ Odd d)
    (hend : ∀ j ∈ range h, EndpointPairAt (independentJ (blockCutoff c h j) m))
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
    have hhcap : independentN q m*2^(64*(j+1)*m) ≤
        2^(256*independentJ (blockCutoff c h j) m) := by
      simp only [independentN,← pow_add,independentJ]
      apply Nat.pow_le_pow_right (by decide)
      have hc' : 1 ≤ blockCutoff c h j := by omega
      have hs := Nat.sub_add_cancel hc'
      have hcq : q+(j+1) ≤ 4*(blockCutoff c h j-1) := by omega
      nlinarith only [Nat.mul_le_mul_right m hcq]
    exact sum_prime_pair_family_block_endpoint M (independentN t m)
      (independentJ (blockCutoff c h j) m) (independentN q m) j m
      (fun d hd => ⟨(hM d hd).1,(hM d hd).2.2.2.2,(hM d hd).2.2.1⟩)
      hQX hhcap (hend j hj) (hmass j hj)
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

lemma family_block_error_pow_bound (M : Finset ℕ) (q t c h m : ℕ)
    (heq : q+c+h=t) (hc : 2 ≤ c) (hM : M.card ≤ independentN q m) :
    familyBlockError M c h m ≤ (3*(h : ℝ))*(2 : ℝ)^((64*t-1)*m) := by
  have hcard : (M.card : ℝ) ≤ (2 : ℝ)^(64*q*m) := by exact_mod_cast hM
  unfold familyBlockError
  rw [mul_sum]
  have hb (j : ℕ) (hj : j ∈ range h) :
      (M.card : ℝ)*((2 : ℝ)^(64*(j+1)*m)*
        ((2 : ℝ)^(64*independentJ (blockCutoff c h j) m)+
          (2 : ℝ)^(16*independentJ (blockCutoff c h j) m)+1)) ≤
        3*(2 : ℝ)^((64*t-1)*m) := by
    let J := independentJ (blockCutoff c h j) m
    have hcut := blockCutoff_properties q t c h j heq (mem_range.mp hj)
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ blockCutoff c h j)
    have hst := Nat.sub_add_cancel (by omega : 1 ≤ 64*t)
    have hexp : 64*q*m+64*(j+1)*m+64*J ≤ (64*t-1)*m := by
      dsimp [J,independentJ]
      nlinarith only [congrArg (fun z : ℕ => z*m) hs,
        congrArg (fun z : ℕ => z*m) hcut.2,congrArg (fun z : ℕ => z*m) hst,Nat.zero_le m]
    have hp : (2 : ℝ)^(16*J) ≤ (2 : ℝ)^(64*J) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h1 : (1 : ℝ) ≤ (2 : ℝ)^(64*J) := one_le_pow₀ (by norm_num)
    calc
      _ ≤ (2 : ℝ)^(64*q*m)*((2 : ℝ)^(64*(j+1)*m)*(3*(2 : ℝ)^(64*J))) := by
        apply mul_le_mul hcard _ (by positivity) (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        change (2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1 ≤ _
        linarith only [hp,h1]
      _ = 3*(2 : ℝ)^(64*q*m+64*(j+1)*m+64*J) := by simp only [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hexp) (by norm_num)
  apply (sum_le_sum hb).trans_eq
  simp only [sum_const,nsmul_eq_mul,card_range]
  ring

lemma family_block_total_error_bound (M : Finset ℕ) (q t c h m I : ℕ)
    (heq : q+c+h=t) (hc : 2 ≤ c) (hM : M.card ≤ independentN q m) :
    Real.log (independentN t m : ℝ)*
      (familyBlockError M c h m+2*(I : ℝ)*Real.sqrt (independentN t m : ℝ)) ≤
      (64*t*(3*h+2*I) : ℕ)*((m : ℝ)+1)*(2 : ℝ)^((64*t-1)*m) := by
  have he := family_block_error_pow_bound M q t c h m heq hc hM
  have hs := independent_sqrt_pow_bound t m (by omega)
  have hl := independent_log_upper t m
  have he0 : 0 ≤ familyBlockError M c h m := by
    unfold familyBlockError
    positivity
  calc
    _ ≤ (64*(t : ℝ)*((m : ℝ)+1))*
        ((3*(h : ℝ))*(2 : ℝ)^((64*t-1)*m)+2*(I : ℝ)*(2 : ℝ)^((64*t-1)*m)) := by
      gcongr
    _ = _ := by push_cast; ring

end Erdos821
