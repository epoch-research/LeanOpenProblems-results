import Submission.SuccessorProgressionBaseline

/-!
# A surviving local mode in the principal-unit baseline

For the pool {3}, the centered kernel is constant 1/2 on two residue-one
input progressions. Thus Type I control alone does not give a uniform Gram
saving for every pool. This is not a counterexample to Erdős 821, nor to a
possible estimate for suitably rough, growing progression moduli.
-/
open Nat Finset
open scoped Classical BigOperators
namespace Erdos821.AnalyticSieve.SuccessorVaughan
set_option maxHeartbeats 2000000

/-- A balanced finite test rectangle away from the exceptional output 1. -/
def localModeSet (L : ℕ) : Finset ℕ :=
  (range L).image (fun i => 3*i+4)

lemma localModeSet_card (L : ℕ) : (localModeSet L).card=L := by
  rw [localModeSet,Finset.card_image_of_injective]
  · exact card_range L
  · intro i j h
    dsimp only at h
    omega

lemma localModeSet_properties (L r : ℕ) (hr : r ∈ localModeSet L) :
    4 ≤ r ∧ r ≤ 3*L+1 ∧ (r : ZMod 3)=1 := by
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hr
  have hiL := mem_range.mp hi
  refine ⟨by omega,by omega,?_⟩
  push_cast
  rw [show (3 : ZMod 3)=0 by decide,zero_mul,zero_add]
  decide

lemma singleton_three_baseline_difference (n : ℕ) (hn : n ≠ 1)
    (hres : (n : ZMod 3)=1) :
    successorProgressionWeight {3} n-successorProgressionPrincipal {3} n = 1/2 := by
  have hc : n.Coprime 3 := (ZMod.isUnit_iff_coprime n 3).mp (by rw [hres]; exact isUnit_one)
  have hφ : Nat.totient 3=2 := by decide
  unfold successorProgressionWeight successorProgressionPrincipal
  rw [sum_singleton,sum_singleton]
  simp only [removeOneWeight,if_neg hn,residueOneOutput,if_pos hres,principalUnitOutput,
    if_pos hc,hφ,Nat.cast_ofNat]
  norm_num

lemma local_mode_kernel (L r s : ℕ) (hr : r ∈ localModeSet L) (hs : s ∈ localModeSet L) :
    successorKernel (successorProgressionWeight {3}) (successorProgressionPrincipal {3})
      ((3*L+1)^2) r s = 1/2 := by
  obtain ⟨hr4,hrhi,hrmod⟩ := localModeSet_properties L r hr
  obtain ⟨hs4,hshi,hsmod⟩ := localModeSet_properties L s hs
  have hcut : r*s ≤ (3*L+1)^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hrhi hshi
  have hn : r*s ≠ 1 := by nlinarith
  have hres : ((r*s : ℕ) : ZMod 3)=1 := by rw [Nat.cast_mul,hrmod,hsmod,mul_one]
  rw [successorKernel,if_pos hcut]
  exact singleton_three_baseline_difference (r*s) hn hres

/-- Distinct rows on this rectangle have a correlation of order its
full column count, not a power-saving correlation. -/
theorem local_mode_row_gram (L r t : ℕ) (hr : r ∈ localModeSet L) (ht : t ∈ localModeSet L) :
    rowGram (localModeSet L)
      (successorKernel (successorProgressionWeight {3}) (successorProgressionPrincipal {3})
        ((3*L+1)^2)) r t = (L : ℝ)/4 := by
  unfold rowGram
  calc
    _ = ∑ _s ∈ localModeSet L, (1/4 : ℝ) := by
      apply sum_congr rfl
      intro s hs
      rw [local_mode_kernel L r s hr hs,local_mode_kernel L t s ht hs]
      norm_num
    _ = _ := by rw [sum_const,nsmul_eq_mul,localModeSet_card]; ring

/-- Exact fourth-order Gram energy for the surviving modulus-three mode. -/
theorem local_mode_gram_energy (L : ℕ) :
    kernelGramEnergy (localModeSet L) (localModeSet L)
      (successorKernel (successorProgressionWeight {3}) (successorProgressionPrincipal {3})
        ((3*L+1)^2)) = (L : ℝ)^4/16 := by
  unfold kernelGramEnergy
  calc
    _ = ∑ _r ∈ localModeSet L, ∑ _t ∈ localModeSet L, ((L : ℝ)/4)^2 := by
      apply sum_congr rfl
      intro r hr
      exact sum_congr rfl (fun t ht => by rw [local_mode_row_gram L r t hr ht])
    _ = _ := by simp only [sum_const,nsmul_eq_mul,localModeSet_card]; ring

/-- Nevertheless the actual prefix/divisibility discrepancy is bounded
independently of the output scale, as proved for every positive pool. -/
theorem local_mode_divisor_error (Q N : ℕ) :
    outputDivisorError (fun n => successorProgressionWeight {3} n-
      successorProgressionPrincipal {3} n) Q N ≤ (7/2 : ℝ)*Q := by
  have hP : ∀ m ∈ ({3} : Finset ℕ), 0 < m := by
    intro m hm
    have he := mem_singleton.mp hm
    rw [he]
    decide
  have h := progression_pool_divisor_error {3} hP Q N
  have hφ : Nat.totient 3=2 := by decide
  have he : progressionPoolPrefixCost {3}=(7/2 : ℝ) := by
    norm_num [progressionPoolPrefixCost,progressionPrefixCost,hφ]
  rw [he] at h
  convert h using 1
  ring

lemma local_mode_gram_not_small (L : ℕ) (hL : 0 < L) (η : ℝ) (hη : η < 1/16) :
    ¬kernelGramEnergy (localModeSet L) (localModeSet L)
      (successorKernel (successorProgressionWeight {3}) (successorProgressionPrincipal {3})
        ((3*L+1)^2)) ≤ η*(L : ℝ)^4 := by
  rw [local_mode_gram_energy]
  have hLp : (0 : ℝ) < (L : ℝ)^4 := pow_pos (by exact_mod_cast hL) _
  have hh := mul_lt_mul_of_pos_right hη hLp
  intro h
  nlinarith only [hh,h]

end Erdos821.AnalyticSieve.SuccessorVaughan
