import Submission.ThreeCofactorSieve
import Submission.UniformBlockBounds

/-!
# Corrected block sieve bounds at variable cutoffs

The main term retains the ACTUAL cutoff X and the corrected cofactor average.
The upper cutoff used for
cofactor coverage may be a different scale; its use is explicit.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

noncomputable def threeBlockUnitMainAt (X c m : ℕ) : ℝ :=
  (13/5950 : ℝ)*(X : ℝ)*(1+64*(m : ℝ)*Real.log 2)/
    ((independentJ c m : ℝ)*Real.log 2)^2

noncomputable def threeBlockSieveMainAt (X b h m : ℕ) : ℝ :=
  ∑ j ∈ range h, threeBlockUnitMainAt X (blockCutoff b h j) m

lemma family_block_rough_count_le_ambient_three_cutoff (M : Finset ℕ) (r q t b c h m X : ℕ)
    (hXupper : X ≤ independentN (r+b+h) m) (hXlower : independentN t m ≤ X) (hq : q+c+h=t) (_hc : 2 ≤ c) (hh : 1 ≤ h)
    (hM : ∀ d ∈ M, 0 < d ∧ independentN r m ≤ d ∧ d ≤ independentN q m ∧
      d ∈ Nat.smoothNumbers (independentN b m) ∧ Odd d)
    (hM3 : ∀ d ∈ M, ¬3 ∣ d)
    (hend : ∀ j ∈ range h, ThreeEndpointPairUpTo X (independentJ (blockCutoff c h j) m))
    (hmass : ∀ j ∈ range h,
      (∑ k ∈ cofactorBlock j m with Even k, Sieve.threeCorrection k/(k.totient : ℝ)) ≤
        (39/35 : ℝ)*(1+64*(m : ℝ)*Real.log 2)) :
    (∑ d ∈ M, ((roughProgressionPrimes d (independentN b m) X).card : ℝ)) ≤
      threeBlockSieveMainAt X c h m*poolTotientMass M+familyBlockError M c h m := by
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
      threeBlockUnitMainAt X (blockCutoff c h j) m*poolTotientMass M+
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
    exact sum_prime_pair_family_block_ambient_three M X
      (independentJ (blockCutoff c h j) m) (independentN q m) j m
      (fun d hd => ⟨(hM d hd).1,(hM d hd).2.2.2.2,(hM d hd).2.2.1,hM3 d hd⟩)
      hQX (hend j hj) (hmass j hj)
  calc
    _ ≤ ∑ d ∈ M, ∑ j ∈ range h, ∑ k ∈ cofactorBlock j m,
        (primePairCofactorCount X (d*k) : ℝ) := sum_le_sum hpairs
    _ = ∑ j ∈ range h, ∑ d ∈ M, ∑ k ∈ cofactorBlock j m,
        (primePairCofactorCount X (d*k) : ℝ) := sum_comm
    _ ≤ ∑ j ∈ range h, (threeBlockUnitMainAt X (blockCutoff c h j) m*poolTotientMass M+
        (M.card : ℝ)*(2 : ℝ)^(64*(j+1)*m)*
          ((2 : ℝ)^(64*independentJ (blockCutoff c h j) m)+
            (2 : ℝ)^(16*independentJ (blockCutoff c h j) m)+1)) := sum_le_sum hblocks
    _ = _ := by simp only [sum_add_distrib,← sum_mul,mul_assoc,← mul_sum,threeBlockSieveMainAt,familyBlockError]

noncomputable def threeBlockMainLimit (t b h : ℕ) : ℝ :=
  (6/7 : ℝ)*sharpBlockMainLimit t b h

lemma threeBlockMainLimit_nonneg (t b h : ℕ) : 0 ≤ threeBlockMainLimit t b h :=
  mul_nonneg (by norm_num) (sharpBlockMainLimit_nonneg t b h)

lemma threeBlockMainLimit_le_telescoped (t b h : ℕ) (hb : 3 ≤ b) :
    threeBlockMainLimit t b h ≤
      (26624/2975 : ℝ)*(t : ℝ)*h/(((b : ℝ)-2)*((b : ℝ)+h-2)) := by
  have hh := mul_le_mul_of_nonneg_left (sharpBlockMainLimit_le_telescoped t b h hb)
    (by norm_num : (0 : ℝ) ≤ 6/7)
  convert hh using 1
  dsimp [threeBlockMainLimit]
  ring

lemma threeBlockSieveMainAt_eq_scale (X b h m : ℕ) :
    threeBlockSieveMainAt X b h m = (6/7 : ℝ)*sharpBlockSieveMainAt X b h m := by
  unfold threeBlockSieveMainAt sharpBlockSieveMainAt
  rw [mul_sum]
  apply sum_congr rfl
  intro j _hj
  unfold threeBlockUnitMainAt sharpBlockUnitMainAt
  ring

lemma eventually_uniform_three_block_main (q t b h K : ℕ)
    (heq : q+b+h=t) (hb : 2 ≤ b) (hK : 1 ≤ K)
    (a : ℝ) (ha : threeBlockMainLimit t b h < a) :
    ∀ᶠ m : ℕ in atTop, ∀ X : ℕ,
      independentN t m ≤ X → X ≤ K*independentN t m →
      Real.log (X : ℝ)*threeBlockSieveMainAt X b h m ≤ a*X := by
  have ha' : sharpBlockMainLimit t b h < (7/6 : ℝ)*a := by
    dsimp [threeBlockMainLimit] at ha
    linarith only [ha]
  filter_upwards [eventually_uniform_sharp_block_main q t b h K heq hb hK ((7/6 : ℝ)*a) ha']
    with m hm
  intro X hlo hhi
  have hh := mul_le_mul_of_nonneg_left (hm X hlo hhi) (by norm_num : (0 : ℝ) ≤ 6/7)
  rw [threeBlockSieveMainAt_eq_scale]
  convert hh using 1 <;> ring

end Erdos821
