import Submission.SharpFamilyDensity

/-!
# Block sieve bounds at variable cutoffs near the ambient scale

The main term retains the ACTUAL cutoff X. The upper cutoff used for
cofactor coverage may be a different scale; its use is explicit.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

noncomputable def sharpBlockUnitMainAt (X c m : ℕ) : ℝ :=
  (13/5100 : ℝ)*(X : ℝ)*(1+64*(m : ℝ)*Real.log 2)/
    ((independentJ c m : ℝ)*Real.log 2)^2

noncomputable def sharpBlockSieveMainAt (X b h m : ℕ) : ℝ :=
  ∑ j ∈ range h, sharpBlockUnitMainAt X (blockCutoff b h j) m

lemma family_block_rough_count_le_ambient_sharp_cutoff (M : Finset ℕ) (r q t b c h m X : ℕ)
    (hXupper : X ≤ independentN (r+b+h) m) (hXlower : independentN t m ≤ X) (hq : q+c+h=t) (_hc : 2 ≤ c) (hh : 1 ≤ h)
    (hM : ∀ d ∈ M, 0 < d ∧ independentN r m ≤ d ∧ d ≤ independentN q m ∧
      d ∈ Nat.smoothNumbers (independentN b m) ∧ Odd d)
    (hend : ∀ j ∈ range h, TightEndpointPairUpTo X (independentJ (blockCutoff c h j) m))
    (hmass : ∀ j ∈ range h,
      (∑ k ∈ cofactorBlock j m with Even k, 1/(k.totient : ℝ)) ≤
        (13/10 : ℝ)*(1+64*(m : ℝ)*Real.log 2)) :
    (∑ d ∈ M, ((roughProgressionPrimes d (independentN b m) X).card : ℝ)) ≤
      sharpBlockSieveMainAt X c h m*poolTotientMass M+familyBlockError M c h m := by
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
      sharpBlockUnitMainAt X (blockCutoff c h j) m*poolTotientMass M+
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
    exact sum_prime_pair_family_block_ambient_thirteen_tenths M X
      (independentJ (blockCutoff c h j) m) (independentN q m) j m
      (fun d hd => ⟨(hM d hd).1,(hM d hd).2.2.2.2,(hM d hd).2.2.1⟩)
      hQX (hend j hj) (hmass j hj)
  calc
    _ ≤ ∑ d ∈ M, ∑ j ∈ range h, ∑ k ∈ cofactorBlock j m,
        (primePairCofactorCount X (d*k) : ℝ) := sum_le_sum hpairs
    _ = ∑ j ∈ range h, ∑ d ∈ M, ∑ k ∈ cofactorBlock j m,
        (primePairCofactorCount X (d*k) : ℝ) := sum_comm
    _ ≤ ∑ j ∈ range h, (sharpBlockUnitMainAt X (blockCutoff c h j) m*poolTotientMass M+
        (M.card : ℝ)*(2 : ℝ)^(64*(j+1)*m)*
          ((2 : ℝ)^(64*independentJ (blockCutoff c h j) m)+
            (2 : ℝ)^(16*independentJ (blockCutoff c h j) m)+1)) := sum_le_sum hblocks
    _ = _ := by simp only [sum_add_distrib,← sum_mul,mul_assoc,← mul_sum,sharpBlockSieveMainAt,familyBlockError]

end Erdos821
