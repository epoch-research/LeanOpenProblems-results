import FormalConjecturesUtil
import Submission.PrimeDeletionVariance

/-! A uniform upper tail bound for the number of prime divisors in a finite set. -/

namespace Erdos371PrimeDivisorSecondMoment

open Finset Erdos371SmallPrimeAveraging Erdos371PrimeDeletionVariance

noncomputable def divisorCount (s : Finset ℕ) (m : ℕ) : ℕ :=
  (s.filter fun p => p ∣ m).card

noncomputable def badFactors (s : Finset ℕ) (K N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun m => K ≤ divisorCount s m

lemma smallCount_eq (s : Finset ℕ) (n : ℕ) : smallCount s n = (divisorCount s (n+1):ℝ) := by
  simp [smallCount,ind,divisorCount]

lemma badFactors_card (s : Finset ℕ) (K N : ℕ) :
    (badFactors s K N).card = ((range N).filter fun n => K≤divisorCount s (n+1)).card := by
  apply card_bij (fun m _ => m-1)
  · intro m hm
    obtain ⟨hmN,hK⟩ := mem_filter.mp hm
    obtain ⟨hm1,hmN⟩ := mem_Icc.mp hmN
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),by simpa [Nat.sub_add_cancel hm1] using hK⟩
  · intro m hm n hn he
    have hm1 := (mem_Icc.mp (mem_filter.mp hm).1).1
    have hn1 := (mem_Icc.mp (mem_filter.mp hn).1).1
    change m-1=n-1 at he
    omega
  · intro n hn
    obtain ⟨hnN,hK⟩ := mem_filter.mp hn
    have hnlt := mem_range.mp hnN
    exact ⟨n+1,mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,hK⟩,by omega⟩

lemma badFactors_square_bound (s : Finset ℕ) (K N : ℕ) :
    ((badFactors s K N).card:ℝ)*(K:ℝ)^2 ≤ ∑ n ∈ range N, (smallCount s n)^2 := by
  rw [badFactors_card]
  calc
    _ = ∑ n ∈ range N, if K≤divisorCount s (n+1) then (K:ℝ)^2 else 0 := by
      rw [← sum_filter]
      simp
    _ ≤ _ := by
      apply sum_le_sum
      intro n _
      split_ifs with h
      · rw [smallCount_eq]
        exact pow_le_pow_left₀ (Nat.cast_nonneg K) (by exact_mod_cast h) 2
      · positivity

/-- No independence assumption is used: joint divisibility counts have
nonpositive floor error. -/
theorem badFactors_card_bound (s : Finset ℕ) (hs : ∀ p∈s,p.Prime)
    {K : ℕ} (hK : 0<K) (N : ℕ) :
    ((badFactors s K N).card:ℝ) ≤ (N:ℝ)*(mass s^2+mass s)/(K:ℝ)^2 := by
  by_cases hN : N=0
  · subst N
    simp [badFactors]
  have hNr : (0:ℝ)<N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  have hKr : (0:ℝ)<K := by exact_mod_cast hK
  have hu := mean_smallCount_sq_upper s hs (Nat.pos_of_ne_zero hN)
  rw [mean] at hu
  have hh := (div_le_iff₀ hNr).mp hu
  apply (le_div_iff₀ (sq_pos_of_pos hKr)).mpr
  exact (badFactors_square_bound s K N).trans (by nlinarith)

end Erdos371PrimeDivisorSecondMoment

#print axioms Erdos371PrimeDivisorSecondMoment.badFactors_card_bound
