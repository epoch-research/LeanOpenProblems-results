import FormalConjecturesUtil
import Submission.PrimeEnergy

/-! Exact cancellation at local peaks. The remaining monotone-triple signs
are not asserted to have mean zero. -/

namespace Erdos371PeakCancellation

open Finset Erdos371PrimeDiscrepancy Erdos371PrimeEnergy

attribute [local instance] Classical.propDecidable

def entry (p n : ℕ) : ℤ := if P (n+1)=p ∧ P n<p then 1 else 0

def exit (p n : ℕ) : ℤ := if P n=p ∧ P (n+1)<p then 1 else 0

def monotoneTriple (n : ℕ) : Prop :=
  (P n<P (n+1) ∧ P (n+1)<P (n+2)) ∨
  (P (n+2)<P (n+1) ∧ P (n+1)<P n)

noncomputable def tripleSign (n : ℕ) : ℤ :=
  if P n<P (n+1) ∧ P (n+1)<P (n+2) then 1
  else if P (n+2)<P (n+1) ∧ P (n+1)<P n then -1 else 0

noncomputable def through (p n : ℕ) : ℤ :=
  if P (n+1)=p then tripleSign n else 0

noncomputable def middleCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter monotoneTriple).card

lemma group_eq_entry_sub_exit (p N : ℕ) :
    group p N = ∑ n ∈ Finset.range N, (entry p n-exit p n) := by
  rw [Finset.sum_sub_distrib]
  simpa [entry,exit] using group_eq_counts p N

lemma through_eq_entry_sub_exit (p n : ℕ) :
    through p n = entry p n-exit p (n+1) := by
  have hleft := consecutive_ne n
  have hright := consecutive_ne (n+1)
  simp only [show n+1+1=n+2 by omega] at hright
  unfold through tripleSign entry exit
  simp only [show n+1+1=n+2 by omega]
  split_ifs <;> omega

lemma exit_zero {p : ℕ} (hp : p.Prime) : exit p 0=0 := by
  simp [exit,P,hp.ne_zero.symm]

lemma exit_nonneg (p n : ℕ) : 0≤exit p n := by
  unfold exit
  split_ifs <;> norm_num

lemma exit_le_single (p n : ℕ) : exit p n ≤ if P n=p then 1 else 0 := by
  unfold exit
  split_ifs <;> omega

/-- All local peaks have disappeared from the sum on the right. -/
theorem group_eq_through_sum {p : ℕ} (hp : p.Prime) (N : ℕ) :
    group p N = (∑ n ∈ Finset.range N,through p n)+exit p N := by
  simp_rw [through_eq_entry_sub_exit]
  rw [Finset.sum_sub_distrib,group_eq_entry_sub_exit,Finset.sum_sub_distrib]
  have h := Finset.sum_range_succ' (exit p) N
  rw [Finset.sum_range_succ,exit_zero hp] at h
  omega

lemma tripleSign_abs (n : ℕ) :
    |tripleSign n| = if monotoneTriple n then 1 else 0 := by
  unfold tripleSign monotoneTriple
  split_ifs <;> simp_all <;> omega

lemma through_abs (p n : ℕ) :
    |through p n| = if P (n+1)=p then (if monotoneTriple n then 1 else 0) else 0 := by
  by_cases h : P (n+1)=p
  · simp only [through,if_pos h,tripleSign_abs]
  · simp only [through,if_neg h,abs_zero]

lemma through_abs_sum_le (s : Finset ℕ) (n : ℕ) :
    (∑ p ∈ s,|through p n|) ≤ if monotoneTriple n then 1 else 0 := by
  simp only [through_abs,Finset.sum_ite_eq]
  split_ifs <;> omega

lemma exit_sum_le (s : Finset ℕ) (N : ℕ) :
    (∑ p ∈ s,exit p N) ≤ 1 := by
  have h := Finset.sum_le_sum (s := s) (fun p _ => exit_le_single p N)
  simp only [Finset.sum_ite_eq] at h
  split_ifs at h <;> omega

/-- An unconditional refinement of the bound by the full interval length.
It is not a little-o estimate: monotone triples have not been shown rare. -/
theorem sum_group_abs_le_middle (s : Finset ℕ) (hs : ∀ p ∈ s,p.Prime) (N : ℕ) :
    (∑ p ∈ s,|group p N|) ≤ (middleCount N:ℤ)+1 := by
  calc
    _ ≤ ∑ p ∈ s, ((∑ n ∈ Finset.range N,|through p n|)+exit p N) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [group_eq_through_sum (hs p hp)]
      exact (abs_add_le _ _).trans (add_le_add
        (Finset.abs_sum_le_sum_abs _ _) (le_of_eq (abs_of_nonneg (exit_nonneg p N))))
    _ = (∑ n ∈ Finset.range N,∑ p ∈ s,|through p n|)+(∑ p ∈ s,exit p N) := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
    _ ≤ (∑ n ∈ Finset.range N,if monotoneTriple n then (1:ℤ) else 0)+1 := by
      exact add_le_add (Finset.sum_le_sum (fun n _ => through_abs_sum_le s n)) (exit_sum_le s N)
    _ = _ := by simp [middleCount]

end Erdos371PeakCancellation

#print axioms Erdos371PeakCancellation.group_eq_through_sum
#print axioms Erdos371PeakCancellation.sum_group_abs_le_middle
