import FormalConjecturesUtil

/-!
# A character obstruction to arithmetic covering systems

This is a sufficient criterion for noncoverage, not a resolution of Erdős 7.
-/

namespace Erdos7ZeroSum
open Finset

private theorem char_sum {ι : Type*} {N : ℕ} [NeZero N]
    (s : Finset ι) (f : ι → ZMod N) :
    ZMod.stdAddChar (∑ i ∈ s, f i) = ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      AddChar.map_add_eq_mul, ih]

/-- If no nonempty subset of the frequencies sums to zero, then the
corresponding translated character kernels cannot cover `ZMod N`. -/
theorem not_cover_character_kernels {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] (k a : ι → ZMod N)
    (hk : ∀ s : Finset ι, s.Nonempty → ∑ i ∈ s, k i ≠ 0) :
    ¬ (∀ x : ZMod N, ∃ i, k i * (x - a i) = 0) := by
  classical
  intro hc
  let χ : AddChar (ZMod N) ℂ := ZMod.stdAddChar
  let F (x : ZMod N) : ℂ := ∏ i, (1 - χ (k i * (x - a i)))
  have hF (x : ZMod N) : F x = 0 := by
    obtain ⟨i, hi⟩ := hc x
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [hi, AddChar.map_zero_eq_one, sub_self]
  have heval (s : Finset ι) (x : ZMod N) :
      (∏ i ∈ s, -χ (k i * (x - a i))) =
        (∏ i ∈ s, -χ (-(k i * a i))) * χ ((∑ i ∈ s, k i) * x) := by
    have ht (i : ι) : -χ (k i * (x - a i)) =
        (-χ (-(k i * a i))) * χ (k i * x) := by
      have he : k i * (x - a i) = -(k i * a i) + k i * x := by ring
      rw [he, AddChar.map_add_eq_mul, neg_mul]
    simp_rw [ht]
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.sum_mul]
    exact (char_sum s (fun i => k i * x)).symm
  have hs (s : Finset ι) (hne : s ≠ ∅) :
      (∑ x : ZMod N, ∏ i ∈ s, -χ (k i * (x - a i))) = 0 := by
    simp_rw [heval]
    rw [← Finset.mul_sum]
    have hz : (∑ x : ZMod N, χ ((∑ i ∈ s, k i) * x)) = 0 :=
      AddChar.sum_eq_zero_of_ne_one
        (ZMod.isPrimitive_stdAddChar N (hk s (Finset.nonempty_iff_ne_empty.mpr hne)))
    rw [hz, mul_zero]
  have hsum : (∑ x : ZMod N, F x) = (N : ℂ) := by
    simp only [F, sub_eq_add_neg, Finset.prod_one_add]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single ∅]
    · simp [ZMod.card]
    · intro s _ hne
      simpa only [sub_eq_add_neg] using hs s hne
    · simp
  simp only [hF, Finset.sum_const_zero] at hsum
  exact (Nat.cast_ne_zero.mpr (NeZero.ne N) : (N : ℂ) ≠ 0) hsum.symm

/-- Frequencies annihilated by the moduli, with no nonempty zero subset sum,
certify that no selection of residue classes with those moduli covers. -/
theorem not_arithmetic_cover {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] (m : ι → ℕ) (a : ι → ℤ) (k : ι → ZMod N)
    (horder : ∀ i, (m i : ZMod N) * k i = 0)
    (hk : ∀ s : Finset ι, s.Nonempty → ∑ i ∈ s, k i ≠ 0) :
    ¬ (∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i) := by
  intro hc
  apply not_cover_character_kernels k (fun i => (a i : ZMod N)) hk
  intro x
  obtain ⟨i, z, hz⟩ := hc (x.val : ℤ)
  refine ⟨i, ?_⟩
  have he : x - (a i : ZMod N) = (m i : ZMod N) * (z : ZMod N) := by
    have hcast := congrArg (fun t : ℤ => (t : ZMod N)) hz
    simpa using hcast
  rw [he, ← mul_assoc, mul_comm (k i) (m i : ZMod N), horder i, zero_mul]

/-- Every arithmetic cover forces a nonempty zero subset sum for every
choice of frequencies annihilated by its moduli. -/
theorem cover_forces_zero_subset_sum {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] (m : ι → ℕ) (a : ι → ℤ) (k : ι → ZMod N)
    (horder : ∀ i, (m i : ZMod N) * k i = 0)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i) :
    ∃ s : Finset ι, s.Nonempty ∧ ∑ i ∈ s, k i = 0 := by
  classical
  by_contra h
  push_neg at h
  exact not_arithmetic_cover m a k horder h hc

#print axioms not_cover_character_kernels
#print axioms not_arithmetic_cover
#print axioms cover_forces_zero_subset_sum
end Erdos7ZeroSum
