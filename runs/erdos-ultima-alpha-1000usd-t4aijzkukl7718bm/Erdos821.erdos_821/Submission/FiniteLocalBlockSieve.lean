import Submission.FiniteLocalCofactorSieve
import Submission.UniformBlockBounds

/-!
# Variable-cutoff block bounds with all fixed local factors retained

The actual cutoff is retained in the main term. The cofactor coefficient
is localAverageConstant D/510. The uniform error budget is unchanged.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

noncomputable def finiteBlockUnitMainAt (D X c m : ℕ) : ℝ :=
  (Sieve.localAverageConstant D/510)*(X : ℝ)*(1+64*(m : ℝ)*Real.log 2)/
    ((independentJ c m : ℝ)*Real.log 2)^2

noncomputable def finiteBlockSieveMainAt (D X b h m : ℕ) : ℝ :=
  ∑ j ∈ range h, finiteBlockUnitMainAt D X (blockCutoff b h j) m

lemma family_block_rough_count_le_ambient_finite_cutoff (M : Finset ℕ) (D r q t b c h m X : ℕ)
    (hXupper : X ≤ independentN (r+b+h) m) (hXlower : independentN t m ≤ X) (hq : q+c+h=t) (_hc : 2 ≤ c) (hh : 1 ≤ h)
    (hM : ∀ d ∈ M, 0 < d ∧ independentN r m ≤ d ∧ d ≤ independentN q m ∧
      d ∈ Nat.smoothNumbers (independentN b m) ∧ Odd d)
    (hMD : ∀ d ∈ M, ∀ p ∈ Sieve.retainedPrimePool D, ¬p ∣ d)
    (hend : ∀ j ∈ range h, FiniteEndpointPairUpTo (Sieve.retainedPrimePool D) X (independentJ (blockCutoff c h j) m))
    (hmass : ∀ j ∈ range h,
      (∑ k ∈ cofactorBlock j m with Even k, Sieve.finiteLocalCorrection (Sieve.retainedPrimePool D) k/(k.totient : ℝ)) ≤
        Sieve.localAverageConstant D*(1+64*(m : ℝ)*Real.log 2)) :
    (∑ d ∈ M, ((roughProgressionPrimes d (independentN b m) X).card : ℝ)) ≤
      finiteBlockSieveMainAt D X c h m*poolTotientMass M+familyBlockError M c h m := by
  have hpairs (d : ℕ) (hd : d ∈ M) :
      ((roughProgressionPrimes d (independentN b m) X).card : ℝ) ≤
        ∑ j ∈ range h, ∑ k ∈ cofactorBlock j m,
          (primePairCofactorCount X (d*k) : ℝ) := by
    have hX : X ≤ d*2^(64*h*m)*independentN b m := by
      calc
        X ≤ independentN (r+b+h) m := hXupper
        _ = independentN r m*2^(64*h*m)*independentN b m := by
          simp only [independentN,← pow_add]
          congr 1
          ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hM d hd).2.1)
    have hp : ((roughProgressionPrimes d (independentN b m) X).card : ℝ) ≤
        ∑ k ∈ Icc 1 (2^(64*h*m)), (primePairCofactorCount X (d*k) : ℝ) := by
      exact_mod_cast rough_composite_progression_card_le_pairs X
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
        (primePairCofactorCount X (d*k) : ℝ)) ≤
      finiteBlockUnitMainAt D X (blockCutoff c h j) m*poolTotientMass M+
        (M.card : ℝ)*(2 : ℝ)^(64*(j+1)*m)*
          ((2 : ℝ)^(64*independentJ (blockCutoff c h j) m)+
            (2 : ℝ)^(16*independentJ (blockCutoff c h j) m)+1) := by
    have hjh := mem_range.mp hj
    have hcut := blockCutoff_properties q t c h j hq hjh
    have hQX : independentN q m*2^(64*(j+1)*m) ≤ X := by
      apply le_trans _ hXlower
      simp only [independentN,← pow_add]
      apply Nat.pow_le_pow_right (by decide)
      nlinarith only [congrArg (fun z : ℕ => 64*z*m) hcut.2,Nat.zero_le (blockCutoff c h j*m)]
    exact sum_prime_pair_family_block_ambient_finite M D X
      (independentJ (blockCutoff c h j) m) (independentN q m) j m
      (fun d hd => ⟨(hM d hd).1,(hM d hd).2.2.2.2,(hM d hd).2.2.1,hMD d hd⟩)
      hQX (hend j hj) (hmass j hj)
  calc
    _ ≤ ∑ d ∈ M, ∑ j ∈ range h, ∑ k ∈ cofactorBlock j m,
        (primePairCofactorCount X (d*k) : ℝ) := sum_le_sum hpairs
    _ = ∑ j ∈ range h, ∑ d ∈ M, ∑ k ∈ cofactorBlock j m,
        (primePairCofactorCount X (d*k) : ℝ) := sum_comm
    _ ≤ ∑ j ∈ range h, (finiteBlockUnitMainAt D X (blockCutoff c h j) m*poolTotientMass M+
        (M.card : ℝ)*(2 : ℝ)^(64*(j+1)*m)*
          ((2 : ℝ)^(64*independentJ (blockCutoff c h j) m)+
            (2 : ℝ)^(16*independentJ (blockCutoff c h j) m)+1)) := sum_le_sum hblocks
    _ = _ := by simp only [sum_add_distrib,← sum_mul,mul_assoc,← mul_sum,finiteBlockSieveMainAt,familyBlockError]

noncomputable def finiteBlockMainLimit (D t b h : ℕ) : ℝ :=
  ((10/13 : ℝ)*Sieve.localAverageConstant D)*sharpBlockMainLimit t b h

lemma finiteBlockMainLimit_nonneg (D t b h : ℕ) (hD : 2 ≤ D) :
    0 ≤ finiteBlockMainLimit D t b h := by
  have hc : 0 ≤ Sieve.localAverageConstant D := (by norm_num : (0 : ℝ) ≤ 1).trans
    (Sieve.localAverageConstant_one_le D hD)
  exact mul_nonneg (mul_nonneg (by norm_num) hc) (sharpBlockMainLimit_nonneg t b h)

lemma finiteBlockMainLimit_le_telescoped (D t b h : ℕ) (hD : 2 ≤ D) (hb : 3 ≤ b) :
    finiteBlockMainLimit D t b h ≤
      ((2048/255 : ℝ)*Sieve.localAverageConstant D)*(t : ℝ)*h/(((b : ℝ)-2)*((b : ℝ)+h-2)) := by
  have hc : 0 ≤ Sieve.localAverageConstant D := (by norm_num : (0 : ℝ) ≤ 1).trans
    (Sieve.localAverageConstant_one_le D hD)
  have hh := mul_le_mul_of_nonneg_left (sharpBlockMainLimit_le_telescoped t b h hb)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10/13) hc)
  convert hh using 1
  dsimp [finiteBlockMainLimit]
  ring

lemma finiteBlockSieveMainAt_eq_scale (D X b h m : ℕ) :
    finiteBlockSieveMainAt D X b h m =
      ((10/13 : ℝ)*Sieve.localAverageConstant D)*sharpBlockSieveMainAt X b h m := by
  unfold finiteBlockSieveMainAt sharpBlockSieveMainAt
  rw [mul_sum]
  apply sum_congr rfl
  intro j _hj
  unfold finiteBlockUnitMainAt sharpBlockUnitMainAt
  ring

lemma eventually_uniform_finite_block_main (D q t b h K : ℕ)
    (hD : 2 ≤ D) (heq : q+b+h=t) (hb : 2 ≤ b) (hK : 1 ≤ K)
    (a : ℝ) (ha : finiteBlockMainLimit D t b h < a) :
    ∀ᶠ m : ℕ in atTop, ∀ X : ℕ,
      independentN t m ≤ X → X ≤ K*independentN t m →
      Real.log (X : ℝ)*finiteBlockSieveMainAt D X b h m ≤ a*X := by
  let s := (10/13 : ℝ)*Sieve.localAverageConstant D
  have hC : 0 < Sieve.localAverageConstant D := (by norm_num : (0 : ℝ)<1).trans_le
    (Sieve.localAverageConstant_one_le D hD)
  have hs : 0<s := mul_pos (by norm_num) hC
  have ha' : sharpBlockMainLimit t b h < a/s := by
    apply (lt_div_iff₀ hs).mpr
    simpa only [finiteBlockMainLimit,mul_comm] using ha
  filter_upwards [eventually_uniform_sharp_block_main q t b h K heq hb hK (a/s) ha'] with m hm
  intro X hlo hhi
  rw [finiteBlockSieveMainAt_eq_scale]
  calc
    _ = s*(Real.log (X : ℝ)*sharpBlockSieveMainAt X b h m) := by dsimp [s]; ring
    _ ≤ s*((a/s)*X) := mul_le_mul_of_nonneg_left (hm X hlo hhi) hs.le
    _ = _ := by field_simp

end Erdos821
