import FormalConjecturesUtil
import Submission.SmoothDensity
import Submission.CofactorDensity
import Submission.Explore

/-! Fixed windows have distinct largest prime factors outside a density-zero set.
This does not assert that the different orderings have equal densities. -/

namespace Erdos371ShiftedTies

open Erdos371Exploration Erdos371CofactorDensity

lemma equal_shift_maxPrimeFac_bounded {n h : ℕ} (hh : 0 < h)
    (he : Nat.maxPrimeFac n = Nat.maxPrimeFac (n + h)) : Nat.maxPrimeFac n ≤ h := by
  have hd : Nat.maxPrimeFac n ∣ n + h := by
    rw [he]
    exact Nat.maxPrimeFac_dvd
  have hd' : Nat.maxPrimeFac n ∣ h :=
    (Nat.dvd_add_iff_right Nat.maxPrimeFac_dvd).2 hd
  exact Nat.le_of_dvd hh hd'

lemma fixed_shift_ties_hasDensity_zero {h : ℕ} (hh : 0 < h) :
    {n | Nat.maxPrimeFac n = Nat.maxPrimeFac (n + h)}.HasDensity 0 := by
  apply density_zero_of_subset _ (bounded_maxPrimeFac_hasDensity_zero h)
  intro n hn
  exact equal_shift_maxPrimeFac_bounded hh hn

lemma density_zero_shift_add {S : Set ℕ} (hS : S.HasDensity 0) (k : ℕ) :
    {n | n + k ∈ S}.HasDensity 0 := by
  induction k with
  | zero => simpa using hS
  | succ k ih =>
      simpa only [Set.mem_setOf_eq, Nat.add_right_comm, Nat.succ_eq_add_one] using
        (density_zero_shift (S := {n | n + k ∈ S}) ih)

lemma density_zero_finite_union {ι : Type*} (s : Finset ι) (A : ι → Set ℕ)
    (hA : ∀ i ∈ s, (A i).HasDensity 0) :
    {n | ∃ i ∈ s, n ∈ A i}.HasDensity 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have he : {n | ∃ i ∈ insert a s, n ∈ A i} = A a ∪ {n | ∃ i ∈ s, n ∈ A i} := by
        ext n
        simp
      rw [he]
      exact density_zero_union (hA a (Finset.mem_insert_self a s))
        (ih (fun i hi => hA i (Finset.mem_insert_of_mem hi)))

lemma duplicate_window_hasDensity_zero (L : ℕ) :
    {n | ∃ i ≤ L, ∃ j ≤ L, i < j ∧
      Nat.maxPrimeFac (n + i) = Nat.maxPrimeFac (n + j)}.HasDensity 0 := by
  have hU := density_zero_finite_union (Finset.range (L + 1))
    (fun i => {n | Nat.maxPrimeFac (n + i) ≤ L})
    (fun i _ => density_zero_shift_add (bounded_maxPrimeFac_hasDensity_zero L) i)
  apply density_zero_of_subset _ hU
  rintro n ⟨i, hi, j, hj, hij, he⟩
  refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
  have he' : Nat.maxPrimeFac (n + i) = Nat.maxPrimeFac (n + i + (j - i)) := by
    have hx : n + i + (j - i) = n + j := by omega
    rwa [hx]
  exact (equal_shift_maxPrimeFac_bounded (by omega : 0 < j - i) he').trans (by omega)

lemma distinct_window_hasDensity_one (L : ℕ) :
    {n | ∀ i ≤ L, ∀ j ≤ L, i < j →
      Nat.maxPrimeFac (n + i) ≠ Nat.maxPrimeFac (n + j)}.HasDensity 1 := by
  have h := hasDensity_compl (duplicate_window_hasDensity_zero L)
  simpa only [sub_zero, Set.compl_setOf, not_exists, not_and] using h

end Erdos371ShiftedTies

#print axioms Erdos371ShiftedTies.fixed_shift_ties_hasDensity_zero
#print axioms Erdos371ShiftedTies.distinct_window_hasDensity_one
