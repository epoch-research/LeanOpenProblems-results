import FormalConjecturesUtil
import Submission.ProductTransportFibers
import Submission.OffDiagonalEnergy

/-! An exact weighted image formula for the winning-prime energy.
It does not estimate the signed image sum at the strength required for Erdős 371. -/

namespace Erdos371ProductEnergyTransport

open Finset Erdos371PrimeDiscrepancy Erdos371PrimeEnergy Erdos371OffDiagonalEnergy
open Erdos371ProductSignTransport Erdos371ProductTransportFibers

lemma winner_one : winner 1=2 := by decide +kernel

lemma winner_eq_two_iff (n : ℕ) : winner n=2 ↔ n=1 := by
  by_cases h0 : n=0
  · subst n
    decide +kernel
  by_cases h1 : n=1
  · subst n
    decide +kernel
  have hh := winner_gt_two (show 1<n by omega)
  omega

lemma correlation_transport (n m : ℕ) : correlation n m =
    (if n=1 ∧ m=1 then (1:ℝ) else 0) -
      (if 1<n ∧ 1 < m ∧ winner n=winner m then (sign (transport n m):ℝ) else 0) := by
  by_cases h0 : n=0
  · subst n
    simp [correlation]
  by_cases h0' : m=0
  · subst m
    simp [correlation]
  by_cases h1 : n=1
  · subst n
    by_cases h1' : m=1
    · subst m
      norm_num [correlation,sign,P]
    · have hw : winner 1≠winner m := by rw [winner_one]; exact Ne.symm ((winner_eq_two_iff m).not.mpr h1')
      simp [correlation,hw,h1']
  by_cases h1' : m=1
  · subst m
    have hw : winner n≠winner 1 := by rw [winner_one]; exact (winner_eq_two_iff n).not.mpr h1
    simp [correlation,hw,h1]
  have hn : 1<n := by omega
  have hm : 1 < m := by omega
  by_cases hw : winner n=winner m
  · have ht := (transport_sign_and_winner hn hm hw).1
    have hc : (sign (transport n m):ℝ)= -((sign n:ℝ)*(sign m:ℝ)) := by exact_mod_cast ht
    simp only [correlation,show 0<n by omega,show 0 < m by omega,hw,hn,hm,h1,h1',
      and_self,if_true,if_false,zero_sub,hc,neg_neg]
  · simp [correlation,hw,hn,hm,h1,h1']

noncomputable def imageSum (N : ℕ) : ℝ :=
  ∑ t ∈ range (N^2+1), ((allFiber N t).card:ℝ)*(sign t:ℝ)

lemma imageSum_eq_pair_sum (N : ℕ) :
    imageSum N=∑ nm ∈ allPairs N, (sign (transport nm.1 nm.2):ℝ) := by
  have hm : ∀ nm∈allPairs N, transport nm.1 nm.2∈range (N^2+1) := by
    intro nm hnm
    have hh := mem_allPairs hnm
    exact mem_range.mpr (Nat.lt_succ_of_le (transport_bound hh.1 hh.2.1))
  rw [← sum_fiberwise_of_maps_to hm (fun nm => (sign (transport nm.1 nm.2):ℝ))]
  unfold imageSum
  apply sum_congr rfl
  intro t ht
  have he : (∑ nm ∈ allPairs N with transport nm.1 nm.2=t,
      (sign (transport nm.1 nm.2):ℝ)) =
      ∑ _nm ∈ allPairs N with transport _nm.1 _nm.2=t, (sign t:ℝ) := by
    apply sum_congr rfl
    intro nm hnm
    rw [(mem_filter.mp hnm).2]
  rw [he]
  simp [allFiber]

/-- All comparisons involving the input 1 contribute the single correction;
all remaining energy is the negative transported signed sum. -/
theorem energy_eq_image_sum (N : ℕ) :
    energy N=(if 1<N then (1:ℝ) else 0)-imageSum N := by
  rw [energy_eq_double_sum]
  simp_rw [correlation_transport,sum_sub_distrib]
  rw [imageSum_eq_pair_sum]
  have he : (∑ n∈range N,∑ m∈range N,if n=1 ∧ m=1 then (1:ℝ) else 0)=
      if 1<N then 1 else 0 := by
    simp [ite_and,sum_ite_irrel,Finset.mem_range]
  rw [he]
  congr 1
  simp [allPairs,Finset.sum_filter,Finset.sum_product]

lemma group_two (N : ℕ) : group 2 N=if 1<N then 1 else 0 := by
  have hs : sign 1=1 := by decide +kernel
  simp [group,winner_eq_two_iff,Finset.mem_range,hs]

/-- This nonpositive weighted sum is an exact consequence of nonnegative energy.
It is not a bound for the unweighted comparison sum. -/
theorem imageSum_nonpos (N : ℕ) : imageSum N≤0 := by
  by_cases hN : 1<N
  · have hp : 2∈(N+1).primesBelow := Nat.mem_primesBelow.mpr ⟨by omega,by decide⟩
    have hle : (group 2 N:ℝ)^2≤energy N :=
      Finset.single_le_sum (fun p _ => sq_nonneg (group p N:ℝ)) hp
    rw [group_two,if_pos hN] at hle
    rw [energy_eq_image_sum,if_pos hN] at hle
    norm_num at hle
    linarith
  · interval_cases N <;> norm_num [imageSum,allFiber,allPairs]

end Erdos371ProductEnergyTransport

#print axioms Erdos371ProductEnergyTransport.energy_eq_image_sum
#print axioms Erdos371ProductEnergyTransport.imageSum_nonpos
