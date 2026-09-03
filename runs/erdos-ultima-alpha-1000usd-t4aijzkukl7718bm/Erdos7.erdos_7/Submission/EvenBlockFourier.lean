import Submission.FourierSubsetObstruction

/-! A conditional Fourier noncoverage certificate. The zero-sum subsets may
form a Boolean family of disjoint even blocks; they need not be just empty.
No universal construction of these blocks for odd distinct moduli is asserted. -/
namespace Erdos7EvenBlockFourier
open Finset
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma mem_union_blocks {I J : Type*} [DecidableEq I] [DecidableEq J]
    (B : J → Finset I) (hd : Pairwise (fun j l => Disjoint (B j) (B l)))
    (s : Finset J) (j : J) (i : I) (hi : i ∈ B j) :
    i ∈ s.biUnion B ↔ j ∈ s := by
  constructor
  · intro h
    obtain ⟨l, hl, hil⟩ := Finset.mem_biUnion.mp h
    by_cases hj : j = l
    · simpa [hj] using hl
    · exact False.elim (Finset.disjoint_left.mp (hd hj) hi hil)
  · intro hj
    exact Finset.mem_biUnion.mpr ⟨j, hj, hi⟩

lemma union_blocks_injective {I J : Type*} [DecidableEq I] [DecidableEq J]
    (B : J → Finset I) (hd : Pairwise (fun j l => Disjoint (B j) (B l)))
    (hne : ∀ j, (B j).Nonempty) :
    Function.Injective (fun s : Finset J => s.biUnion B) := by
  intro s t h
  dsimp only at h
  ext j
  obtain ⟨i, hi⟩ := hne j
  rw [← mem_union_blocks B hd s j i hi, ← mem_union_blocks B hd t j i hi, h]

private lemma char_sum {I : Type*} {N : ℕ} [NeZero N]
    (s : Finset I) (f : I → ZMod N) :
    ZMod.stdAddChar (∑ i ∈ s, f i) = ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      AddChar.map_add_eq_mul, ih]

lemma signed_phase_eq_prod {I : Type*} {N : ℕ} [NeZero N]
    (k a : I → ZMod N) (s : Finset I) :
    (-1 : ℂ) ^ s.card * ZMod.stdAddChar (-(∑ i ∈ s, k i * a i)) =
      ∏ i ∈ s, -ZMod.stdAddChar (-(k i * a i)) := by
  symm
  rw [Finset.prod_neg]
  congr 1
  rw [← char_sum]
  congr 1
  simp

lemma phase_union_even_blocks {I J : Type*} [DecidableEq I]
    {N : ℕ} [NeZero N] (k a : I → ZMod N) (B : J → Finset I)
    (hd : Pairwise (fun j l => Disjoint (B j) (B l)))
    (heven : ∀ j, Even (B j).card) (s : Finset J) :
    (-1 : ℂ) ^ (s.biUnion B).card *
        ZMod.stdAddChar (-(∑ i ∈ s.biUnion B, k i * a i)) =
      ∏ j ∈ s, ZMod.stdAddChar (-(∑ i ∈ B j, k i * a i)) := by
  rw [signed_phase_eq_prod]
  rw [Finset.prod_biUnion (fun j _ l _ hjl => hd hjl)]
  apply Finset.prod_congr rfl
  intro j _
  rw [← signed_phase_eq_prod, (heven j).neg_one_pow, one_mul]

lemma phase_union_blocks {I J : Type*} [DecidableEq I]
    {N : ℕ} [NeZero N] (k a : I → ZMod N) (B : J → Finset I)
    (hd : Pairwise (fun j l => Disjoint (B j) (B l))) (s : Finset J) :
    (-1 : ℂ) ^ (s.biUnion B).card *
        ZMod.stdAddChar (-(∑ i ∈ s.biUnion B, k i * a i)) =
      ∏ j ∈ s, ((-1 : ℂ) ^ (B j).card *
        ZMod.stdAddChar (-(∑ i ∈ B j, k i * a i))) := by
  rw [signed_phase_eq_prod]
  rw [Finset.prod_biUnion (fun j _ l _ hjl => hd hjl)]
  apply Finset.prod_congr rfl
  intro j _
  exact (signed_phase_eq_prod k a (B j)).symm

/-- Without an evenness assumption, the block signs remain in the factors. -/
theorem zero_coefficient_general_blocks {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {N : ℕ} [NeZero N]
    (k a : I → ZMod N) (B : J → Finset I)
    (hd : Pairwise (fun j l => Disjoint (B j) (B l)))
    (hne : ∀ j, (B j).Nonempty)
    (hz : ∀ u : Finset I, (∑ i ∈ u, k i = 0) ↔
      ∃ s : Finset J, s.biUnion B = u) :
    (∑ u ∈ (Finset.univ : Finset I).powerset,
      if ∑ i ∈ u, k i = 0 then
        (-1 : ℂ) ^ u.card * ZMod.stdAddChar (-(∑ i ∈ u, k i * a i)) else 0) =
      ∏ j : J, (1 + (-1 : ℂ) ^ (B j).card *
        ZMod.stdAddChar (-(∑ i ∈ B j, k i * a i))) := by
  classical
  have hsets : (Finset.univ : Finset I).powerset.filter (fun u => ∑ i ∈ u, k i = 0) =
      (Finset.univ : Finset J).powerset.image (fun s => s.biUnion B) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
      true_and, Finset.mem_image, hz]
  rw [← Finset.sum_filter, hsets]
  rw [Finset.sum_image (fun s _ t _ h => union_blocks_injective B hd hne h)]
  simp_rw [phase_union_blocks k a B hd]
  exact (Finset.prod_one_add Finset.univ).symm

lemma one_add_char_ne_zero {N : ℕ} [NeZero N] (hodd : Odd N) (u : ZMod N) :
    1 + ZMod.stdAddChar u ≠ 0 := by
  intro h
  apply Erdos7SubsetFourier.char_ne_neg hodd 0 u
  simpa using eq_neg_of_add_eq_zero_left h

/-- Exact factorization of the coefficient at frequency zero. -/
theorem zero_coefficient_factorization {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {N : ℕ} [NeZero N]
    (k a : I → ZMod N) (B : J → Finset I)
    (hd : Pairwise (fun j l => Disjoint (B j) (B l)))
    (hne : ∀ j, (B j).Nonempty) (heven : ∀ j, Even (B j).card)
    (hz : ∀ u : Finset I, (∑ i ∈ u, k i = 0) ↔
      ∃ s : Finset J, s.biUnion B = u) :
    (∑ u ∈ (Finset.univ : Finset I).powerset,
      if ∑ i ∈ u, k i = 0 then
        (-1 : ℂ) ^ u.card * ZMod.stdAddChar (-(∑ i ∈ u, k i * a i)) else 0) =
      ∏ j : J, (1 + ZMod.stdAddChar (-(∑ i ∈ B j, k i * a i))) := by
  classical
  have hsets : (Finset.univ : Finset I).powerset.filter (fun u => ∑ i ∈ u, k i = 0) =
      (Finset.univ : Finset J).powerset.image (fun s => s.biUnion B) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
      true_and, Finset.mem_image, hz]
  rw [← Finset.sum_filter, hsets]
  rw [Finset.sum_image (fun s _ t _ h => union_blocks_injective B hd hne h)]
  simp_rw [phase_union_even_blocks k a B hd heven]
  exact (Finset.prod_one_add Finset.univ).symm

/-- Arbitrarily many zero-sum subsets are harmless when they are exactly
unions of disjoint even blocks. Odd-order plus factors cannot vanish. -/
theorem not_cover_even_blocks {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {N : ℕ} [NeZero N] (hodd : Odd N)
    (k a : I → ZMod N) (B : J → Finset I)
    (hd : Pairwise (fun j l => Disjoint (B j) (B l)))
    (hne : ∀ j, (B j).Nonempty) (heven : ∀ j, Even (B j).card)
    (hz : ∀ u : Finset I, (∑ i ∈ u, k i = 0) ↔
      ∃ s : Finset J, s.biUnion B = u) :
    ¬ (∀ x : ZMod N, ∃ i, k i * (x - a i) = 0) := by
  intro hc
  have hf := Erdos7SubsetFourier.cover_coefficient_vanishes k a hc 0
  rw [zero_coefficient_factorization k a B hd hne heven hz] at hf
  exact (Finset.prod_ne_zero_iff.mpr (fun j _ => one_add_char_ne_zero hodd _)) hf

/-- A cover must have an odd zero block with vanishing residue phase.
This retains information that is lost by counting zero subsets alone. -/
theorem cover_forces_odd_block_phase {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {N : ℕ} [NeZero N] (hodd : Odd N)
    (k a : I → ZMod N) (B : J → Finset I)
    (hd : Pairwise (fun j l => Disjoint (B j) (B l)))
    (hne : ∀ j, (B j).Nonempty)
    (hz : ∀ u : Finset I, (∑ i ∈ u, k i = 0) ↔
      ∃ s : Finset J, s.biUnion B = u)
    (hc : ∀ x : ZMod N, ∃ i, k i * (x - a i) = 0) :
    ∃ j, Odd (B j).card ∧ ∑ i ∈ B j, k i * a i = 0 := by
  have hf := Erdos7SubsetFourier.cover_coefficient_vanishes k a hc 0
  rw [zero_coefficient_general_blocks k a B hd hne hz] at hf
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hf
  rcases Nat.even_or_odd (B j).card with he | ho
  · rw [he.neg_one_pow, one_mul] at hj
    exact False.elim (one_add_char_ne_zero hodd _ hj)
  · refine ⟨j, ho, ?_⟩
    rw [ho.neg_one_pow, neg_one_mul] at hj
    have hchar : ZMod.stdAddChar (-(∑ i ∈ B j, k i * a i)) = 1 := by
      exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hj)).symm
    have hzero : -(∑ i ∈ B j, k i * a i) = 0 := by
      apply ZMod.injective_stdAddChar
      simpa only [AddChar.map_zero_eq_one] using hchar
    exact neg_eq_zero.mp hzero

/-- Frequencies need only be annihilated by their original moduli. -/
theorem not_arithmetic_cover_even_blocks {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {N : ℕ} [NeZero N] (hodd : Odd N)
    (m : I → ℕ) (a : I → ℤ) (k : I → ZMod N)
    (horder : ∀ i, (m i : ZMod N) * k i = 0) (B : J → Finset I)
    (hd : Pairwise (fun j l => Disjoint (B j) (B l)))
    (hne : ∀ j, (B j).Nonempty) (heven : ∀ j, Even (B j).card)
    (hz : ∀ u : Finset I, (∑ i ∈ u, k i = 0) ↔
      ∃ s : Finset J, s.biUnion B = u) :
    ¬ (∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i) := by
  intro hc
  apply not_cover_even_blocks hodd k (fun i => (a i : ZMod N)) B hd hne heven hz
  intro x
  obtain ⟨i, z, hz⟩ := hc (x.val : ℤ)
  refine ⟨i, ?_⟩
  have he : x - (a i : ZMod N) = (m i : ZMod N) * (z : ZMod N) := by
    have hcast := congrArg (fun t : ℤ => (t : ZMod N)) hz
    simpa using hcast
  rw [he, ← mul_assoc, mul_comm (k i) (m i : ZMod N), horder i, zero_mul]

#print axioms zero_coefficient_general_blocks
#print axioms cover_forces_odd_block_phase
#print axioms zero_coefficient_factorization
#print axioms not_cover_even_blocks
#print axioms not_arithmetic_cover_even_blocks
end Erdos7EvenBlockFourier
