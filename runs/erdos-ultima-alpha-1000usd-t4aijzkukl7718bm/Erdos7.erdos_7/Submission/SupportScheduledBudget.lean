import Submission.SupportPrefixInterpretation

/-! Assembly of a finite prefix and the polynomial continuation, uniformly
in the number of later primes and in all finite exponent caps. -/
namespace Erdos7SupportScheduledBudget
open scoped BigOperators
open Erdos7SupportCompression Erdos7SupportTailIteration Erdos7SupportLowerLaw
open Erdos7SupportPrefixData Erdos7SupportPrefixChecks Erdos7SupportPrefixMetadata
open Erdos7SupportPrefixPotential Erdos7SupportPrefixInterpretation
open Erdos7CompressionSieve Erdos7Distortion
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000

structure Schedule (N : ℕ) (P E : ℕ → ℕ) (C : ℕ → ℚ) : Prop where
  length : 167 ≤ N
  primePrefix : ∀ i : Fin 167,P i=p i
  capPrefix : ∀ i : Fin 167,C i=cap i
  exponentPrefix : ∀ i : Fin 167,12 < E i
  bounds : ∀ i,i < N → 1 < P i ∧ 1 ≤ C i ∧ C i ≤ P i
  tailLarge : ∀ i,167 ≤ i → i ≤ N → 1001 ≤ P i
  tailGap : ∀ i,167 ≤ i → i < N → P i+2 ≤ P (i+1)
  tailCap : ∀ i,167 ≤ i → i < N → C i=5/4

noncomputable def law (N : ℕ) (P E : ℕ → ℕ) (C : ℕ → ℚ) : ℕ → TripleState →₀ ℚ :=
  triplePrefixLaw (fun i : Fin N => E i) (fun i : Fin N => powerTail (P i) (C i) (E i))

lemma law_zero (N : ℕ) (P E : ℕ → ℕ) (C : ℕ → ℚ) : law N P E C 0=tripleInitial := rfl

lemma law_step (N : ℕ) (P E : ℕ → ℕ) (C : ℕ → ℚ) (i : ℕ) (hi : i < N) :
    law N P E C (i+1)=tripleStep (E i) (powerTail (P i) (C i) (E i)) (law N P E C i) := by
  simp only [law,triplePrefixLaw,dif_pos hi]

lemma law_nonneg (N : ℕ) (P E : ℕ → ℕ) (C : ℕ → ℚ) (hs : Schedule N P E C) (t : ℕ) :
    0 ≤ law N P E C t := by
  apply triplePrefixLaw_nonneg
  · intro i
    have h := hs.bounds i i.isLt
    exact powerTail_zero_le_one _ h.1 _ h.2.2 _
  · intro i g _
    have h := hs.bounds i i.isLt
    exact powerTail_decreasing _ h.1 _ (by linarith [h.2.1]) _ _

lemma cost_law (N : ℕ) (P E : ℕ → ℕ) (C : ℕ → ℚ) :
    supportCost (fun i : Fin N => E i) (fun i => powerTail (P i) (C i) (E i))
      (fun i => C i) (fun i => 1/((P i:ℚ)-1)) 2 =
      ∑ i ∈ Finset.range N,pairExpect (law N P E C i)
        (fun x => residual (C i) ((tripleCount x:ℚ)/((P i:ℚ)-1))) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => pairExpect (law N P E C i)
    (fun x => residual (C i) ((tripleCount x:ℚ)/((P i:ℚ)-1)))) N]
  apply Finset.sum_congr rfl
  intro i _
  rw [supportEnvelope_two_eq]
  apply pairExpect_congr
  intro x
  congr 1
  ring

lemma combine_tail (N : ℕ) (P E : ℕ → ℕ) (C : ℕ → ℚ) (hs : Schedule N P E C)
    (hprefix : prefixLoss (law N P E C)+
      pairExpect (law N P E C 167) statePotential/(1000:ℚ)^2 < 24/25) :
    supportCost (fun i : Fin N => E i) (fun i => powerTail (P i) (C i) (E i))
      (fun i => C i) (fun i => 1/((P i:ℚ)-1)) 2 < 24/25 := by
  let μ := law N P E C
  have ht := finite_tail_sum (N-167) (fun i => P (167+i)) (fun i => E (167+i))
    (fun i => μ (167+i)) (fun i hi => law_nonneg N P E C hs (167+i))
    (fun i hi => by
      change 128 ≤ P (167+i)
      have h := hs.tailLarge (167+i) (by omega) (by omega)
      omega)
    (fun i hi => by simpa only [Nat.add_assoc] using hs.tailGap (167+i) (by omega) (by omega))
    (fun i hi => by
      have h := law_step N P E C (167+i) (by omega)
      rw [hs.tailCap (167+i) (by omega) (by omega)] at h
      simpa only [Nat.add_assoc] using h)
  simp only [Nat.add_zero] at ht
  have hP : (1001:ℚ) ≤ P 167 := by exact_mod_cast hs.tailLarge 167 le_rfl hs.length
  have hpot := pairExpect_nonneg (μ 167) (law_nonneg N P E C hs 167) statePotential statePotential_nonneg
  have hden : (1000:ℚ)^2 ≤ ((P 167:ℚ)-1)^2 := by nlinarith
  have htail := ht.trans (div_le_div_of_nonneg_left hpot (by norm_num : (0:ℚ) < 1000^2) hden)
  let f (i : ℕ) := pairExpect (μ i) (fun x => residual (C i) ((tripleCount x:ℚ)/((P i:ℚ)-1)))
  have hsplit : (∑ i ∈ Finset.range N,f i)=(∑ i ∈ Finset.range 167,f i)+
      ∑ i ∈ Finset.range (N-167),f (167+i) := by
    simpa only [Nat.add_sub_of_le hs.length] using Finset.sum_range_add f 167 (N-167)
  have hfirst : (∑ i ∈ Finset.range 167,f i)=prefixLoss μ := by
    rw [← Fin.sum_univ_eq_sum_range f 167]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f]
    rw [hs.primePrefix i,hs.capPrefix i]
  have hlast : (∑ i ∈ Finset.range (N-167),f (167+i))=
      ∑ i ∈ Finset.range (N-167),pairExpect (μ (167+i)) (stateLoss (P (167+i))) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [f,stateLoss]
    rw [hs.tailCap (167+i) (by omega) (by have := Finset.mem_range.mp hi; omega)]
    rfl
  rw [cost_law]
  change (∑ i ∈ Finset.range N,f i) < 24/25
  rw [hsplit,hfirst,hlast]
  exact (add_le_add le_rfl htail).trans_lt hprefix

/-- All numerical hypotheses are explicit. Once checked, they imply a
uniform budget bound for every finite schedule satisfying the support cap. -/
theorem scheduled_budget (N : ℕ) (P E : ℕ → ℕ) (C : ℕ → ℚ) (hs : Schedule N P E C)
    (hL : ∀ i : Fin 167,∀ j : Fin 180,lowerRow i j)
    (hM : ∀ i : Fin 167,∀ j : Fin 10,momentRow i j)
    (hC : ∀ i : Fin 167,lossRow i)
    (hmargin : totalCost*25*(243*momentScale*1000^2)+tailNumerator 167*25*costScale <
      24*costScale*(243*momentScale*1000^2)) :
    supportCost (fun i : Fin N => E i) (fun i => powerTail (P i) (C i) (E i))
      (fun i => C i) (fun i => 1/((P i:ℚ)-1)) 2 < 24/25 := by
  apply combine_tail N P E C hs
  apply prefix_with_tail (fun i : Fin 167 => E i) (law N P E C) hs.exponentPrefix
    (law_zero N P E C) _ hL hM hC hmargin
  intro i
  have h := law_step N P E C i.val (lt_of_lt_of_le i.isLt hs.length)
  rw [hs.primePrefix i,hs.capPrefix i] at h
  exact h

#print axioms scheduled_budget
end Erdos7SupportScheduledBudget
