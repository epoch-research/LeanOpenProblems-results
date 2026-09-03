import FormalConjecturesUtil

/-!
# Subset-frequency obstructions for odd-order arithmetic covers

These are necessary conditions and sufficient noncoverage criteria, not a
resolution of Erdős Problem 7.
-/

namespace Erdos7SubsetFourier
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

/-- Two character values of odd order are never negatives of one another. -/
theorem char_ne_neg {N : ℕ} [NeZero N] (hodd : Odd N) (u v : ZMod N) :
    ZMod.stdAddChar u ≠ -ZMod.stdAddChar v := by
  have hp (x : ZMod N) : ZMod.stdAddChar x ^ N = 1 := by
    rw [← AddChar.map_nsmul_eq_pow]
    simp [nsmul_eq_mul]
  intro h
  have hh := congrArg (fun z : ℂ => z ^ N) h
  dsimp only at hh
  rw [hodd.neg_pow, hp, hp] at hh
  norm_num at hh

/-- A character-kernel cover makes each coefficient of the subset expansion
vanish, not just its coefficient at frequency zero. -/
theorem cover_coefficient_vanishes {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] (k a : ι → ZMod N)
    (hc : ∀ x : ZMod N, ∃ i, k i * (x - a i) = 0) (b : ZMod N) :
    ∑ s ∈ (Finset.univ : Finset ι).powerset,
      (if ∑ i ∈ s, k i = b then
        (-1 : ℂ) ^ s.card * ZMod.stdAddChar (-(∑ i ∈ s, k i * a i)) else 0) = 0 := by
  classical
  let χ : AddChar (ZMod N) ℂ := ZMod.stdAddChar
  let c (s : Finset ι) : ℂ := ∏ i ∈ s, -χ (-(k i * a i))
  let F (x : ZMod N) : ℂ := ∏ i, (1 - χ (k i * (x - a i)))
  have hF (x : ZMod N) : F x = 0 := by
    obtain ⟨i, hi⟩ := hc x
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [hi, AddChar.map_zero_eq_one, sub_self]
  have heval (s : Finset ι) (x : ZMod N) :
      (∏ i ∈ s, -χ (k i * (x - a i))) * χ (-(b * x)) =
        c s * χ (((∑ i ∈ s, k i) - b) * x) := by
    have ht (i : ι) : -χ (k i * (x - a i)) =
        (-χ (-(k i * a i))) * χ (k i * x) := by
      have he : k i * (x - a i) = -(k i * a i) + k i * x := by ring
      rw [he, AddChar.map_add_eq_mul, neg_mul]
    simp_rw [ht]
    rw [Finset.prod_mul_distrib]
    change (c s * ∏ i ∈ s, χ (k i * x)) * χ (-(b * x)) = _
    rw [← char_sum s (fun i => k i * x), mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    rw [← Finset.sum_mul]
    ring
  have hz (s : Finset ι) :
      (∑ x : ZMod N, χ (((∑ i ∈ s, k i) - b) * x)) =
        if ∑ i ∈ s, k i = b then (N : ℂ) else 0 := by
    split_ifs with h
    · simp only [h, sub_self, zero_mul, AddChar.map_zero_eq_one,
        Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    · exact AddChar.sum_eq_zero_of_ne_one
        (ZMod.isPrimitive_stdAddChar N (sub_ne_zero.mpr h))
  have hexpand : (∑ x : ZMod N, F x * χ (-(b * x))) =
      (N : ℂ) * ∑ s ∈ (Finset.univ : Finset ι).powerset,
        if ∑ i ∈ s, k i = b then c s else 0 := by
    have hprod (x : ZMod N) : F x =
        ∑ s ∈ (Finset.univ : Finset ι).powerset,
          ∏ i ∈ s, -χ (k i * (x - a i)) := by
      unfold F
      simpa only [sub_eq_add_neg] using
        (Finset.prod_one_add (f := fun i => -χ (k i * (x - a i))) Finset.univ)
    simp_rw [hprod, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [heval, ← Finset.mul_sum, hz]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp [mul_comm]
  have hh : (∑ s ∈ (Finset.univ : Finset ι).powerset,
      if ∑ i ∈ s, k i = b then c s else 0) = 0 := by
    have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    apply (mul_eq_zero.mp ?_).resolve_left hn
    rw [← hexpand]
    simp only [hF, zero_mul, Finset.sum_const_zero]
  have hphase (s : Finset ι) : c s =
      (-1 : ℂ) ^ s.card * χ (-(∑ i ∈ s, k i * a i)) := by
    unfold c
    rw [Finset.prod_neg]
    congr 1
    rw [← char_sum]
    congr 1
    simp
  simpa only [hphase] using hh

/-- Two subset representations of a frequency, with equal parity, are
incompatible with a cover of an odd-order cyclic group. -/
theorem not_cover_two_same_sign {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] (hodd : Odd N) (k a : ι → ZMod N)
    (s t : Finset ι) (hst : s ≠ t) (b : ZMod N)
    (hfreq : ∀ u : Finset ι, (∑ i ∈ u, k i = b) ↔ u = s ∨ u = t)
    (hsign : (-1 : ℂ) ^ s.card = (-1 : ℂ) ^ t.card) :
    ¬ (∀ x : ZMod N, ∃ i, k i * (x - a i) = 0) := by
  classical
  intro hc
  have h := cover_coefficient_vanishes k a hc b
  rw [← Finset.sum_filter] at h
  have hf : ((Finset.univ : Finset ι).powerset.filter
      (fun u => ∑ i ∈ u, k i = b)) = {s, t} := by
    ext u
    simp [hfreq]
  rw [hf, Finset.sum_pair hst, ← hsign, ← mul_add] at h
  have hn : (-1 : ℂ) ^ s.card ≠ 0 := pow_ne_zero _ (by norm_num)
  have he := (mul_eq_zero.mp h).resolve_left hn
  exact char_ne_neg hodd _ _ (eq_neg_of_add_eq_zero_left he)

/-- Arithmetic version of the two-representation obstruction. The selected
frequency need not have exact order equal to the corresponding modulus. -/
theorem not_arithmetic_cover_two_same_sign {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] (hodd : Odd N)
    (m : ι → ℕ) (a : ι → ℤ) (k : ι → ZMod N)
    (horder : ∀ i, (m i : ZMod N) * k i = 0)
    (s t : Finset ι) (hst : s ≠ t) (b : ZMod N)
    (hfreq : ∀ u : Finset ι, (∑ i ∈ u, k i = b) ↔ u = s ∨ u = t)
    (hsign : (-1 : ℂ) ^ s.card = (-1 : ℂ) ^ t.card) :
    ¬ (∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i) := by
  intro hc
  apply not_cover_two_same_sign hodd k (fun i => (a i : ZMod N)) s t hst b hfreq hsign
  intro x
  obtain ⟨i, z, hz⟩ := hc (x.val : ℤ)
  refine ⟨i, ?_⟩
  have he : x - (a i : ZMod N) = (m i : ZMod N) * (z : ZMod N) := by
    have hcast := congrArg (fun t : ℤ => (t : ZMod N)) hz
    simpa using hcast
  rw [he, ← mul_assoc, mul_comm (k i) (m i : ZMod N), horder i, zero_mul]

#print axioms char_ne_neg
#print axioms cover_coefficient_vanishes
#print axioms not_cover_two_same_sign
#print axioms not_arithmetic_cover_two_same_sign
end Erdos7SubsetFourier
