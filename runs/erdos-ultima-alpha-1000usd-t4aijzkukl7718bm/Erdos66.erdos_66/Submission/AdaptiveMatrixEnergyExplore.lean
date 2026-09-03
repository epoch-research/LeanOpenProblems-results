import Submission.PairWeightedRootTransferExplore

/-! Why the matrix weights cannot be chosen arbitrarily after the translate:
a nonnegative zero-one matrix can align with that translate's character. -/
namespace Erdos66AdaptiveMatrixEnergy
open Erdos66PairWeightedCharacterEnergy Erdos66PairWeightedRootTransfer
  Erdos66IndexedCharacterEnergy
open scoped Classical
set_option maxHeartbeats 2200000

variable {p : ℕ} [Fact p.Prime]

noncomputable def alignedMatrix (a : ZMod p) (i j : ℕ) : ℝ :=
  (1+(quadraticChar (ZMod p) (a+i):ℝ)*(quadraticChar (ZMod p) (a+j):ℝ))/2

lemma alignedMatrix_zero_one (h : ℕ) (a : ZMod p)
    (ha : ∀ i<h, a+(i:ZMod p)≠0) (i j : ℕ) (hi : i<h) (hj : j<h) :
    alignedMatrix a i j=0 ∨ alignedMatrix a i j=1 := by
  have hi' : ((quadraticChar (ZMod p) (a+i):ℝ))^2=1 := by
    exact_mod_cast quadraticChar_sq_one (ha i hi)
  have hj' : ((quadraticChar (ZMod p) (a+j):ℝ))^2=1 := by
    exact_mod_cast quadraticChar_sq_one (ha j hj)
  rcases sq_eq_one_iff.mp hi' with h₁ | h₁ <;>
    rcases sq_eq_one_iff.mp hj' with h₂ | h₂ <;>
    dsimp only [alignedMatrix] <;> rw [h₁,h₂] <;> norm_num

lemma alignedMatrix_fiber (h : ℕ) (a : ZMod p)
    (ha : ∀ i<h, a+(i:ZMod p)≠0) (q : ℕ) :
    matrixFiber h (alignedMatrix a) a q =
      ∑ ij∈pairFiber h q, alignedMatrix a ij.1 ij.2 := by
  unfold matrixFiber
  apply Finset.sum_congr rfl
  intro ij hij
  obtain ⟨hi,hj,he⟩ := mem_pairFiber.mp hij
  have hi' : ((quadraticChar (ZMod p) (a+ij.1):ℝ))^2=1 := by
    exact_mod_cast quadraticChar_sq_one (ha _ hi)
  have hj' : ((quadraticChar (ZMod p) (a+ij.2):ℝ))^2=1 := by
    exact_mod_cast quadraticChar_sq_one (ha _ hj)
  have hh : ((quadraticChar (ZMod p) (a+ij.1):ℝ)*
      (quadraticChar (ZMod p) (a+ij.2):ℝ))^2=1 := by rw [mul_pow,hi',hj']; norm_num
  dsimp only [alignedMatrix]
  nlinarith only [hh]

lemma alignedMatrix_sum (h : ℕ) (a : ZMod p) :
    matrixSum h (alignedMatrix a) = ((h:ℝ)^2+
      (∑ i∈Finset.range h, (quadraticChar (ZMod p) (a+i):ℝ))^2)/2 := by
  simp only [matrixSum, alignedMatrix]
  simp_rw [←Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one]
  rw [pow_two (∑ i∈Finset.range h, (quadraticChar (ZMod p) (a+i):ℝ)),
    Finset.sum_mul_sum]
  ring

/-- At every fixed admissible translate there is a zero-one pair matrix with
energy at least h^3/8, although its squared mass is at most h^2. -/
theorem alignedMatrix_energy_lower (h : ℕ) (a : ZMod p)
    (ha : ∀ i<h, a+(i:ZMod p)≠0) :
    (h:ℝ)^3 ≤ 8*matrixEnergy h (alignedMatrix a) a := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (2*h))
    (fun _ : ℕ ↦ (1:ℝ)) (matrixFiber h (alignedMatrix a) a)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, Nat.cast_mul, Nat.cast_ofNat] at hcs
  change (∑ q∈Finset.range (2*h), matrixFiber h (alignedMatrix a) a q)^2 ≤
    2*(h:ℝ)*matrixEnergy h (alignedMatrix a) a at hcs
  simp_rw [alignedMatrix_fiber h a ha] at hcs
  rw [sum_pairFiber h (alignedMatrix a)] at hcs
  change (matrixSum h (alignedMatrix a))^2 ≤ _ at hcs
  rw [alignedMatrix_sum] at hcs
  by_cases hh : h=0
  · subst h
    simpa only [Nat.cast_zero, zero_pow (by decide : 3≠0)] using
      mul_nonneg (show (0:ℝ)≤8 by norm_num) (matrixEnergy_nonneg 0 (alignedMatrix a) a)
  · have hhr : (0:ℝ)<h := by exact_mod_cast Nat.pos_of_ne_zero hh
    apply le_of_mul_le_mul_left (a := (h:ℝ)) _ hhr
    have hs := sq_nonneg (∑ i∈Finset.range h, (quadraticChar (ZMod p) (a+i):ℝ))
    have hm := mul_nonneg (sq_nonneg (h:ℝ)) hs
    nlinarith only [hcs,hm,sq_nonneg
      ((∑ i∈Finset.range h, (quadraticChar (ZMod p) (a+i):ℝ))^2)]

lemma alignedMatrix_mass_le (h : ℕ) (a : ZMod p)
    (ha : ∀ i<h, a+(i:ZMod p)≠0) :
    matrixMass h (alignedMatrix a)≤(h:ℝ)^2 := by
  unfold matrixMass
  calc
    _ ≤ ∑ _i∈Finset.range h, ∑ _j∈Finset.range h, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rcases alignedMatrix_zero_one h a ha i j (Finset.mem_range.mp hi)
        (Finset.mem_range.mp hj) with he | he <;> simp [he]
    _ = _ := by simp [pow_two]

/-- A putative uniform energy constant for every later nonnegative bounded
matrix must grow at least linearly with the label count. -/
theorem universal_matrix_budget_requires_large_constant (h : ℕ) (hh : 0<h)
    (a : ZMod p) (ha : ∀ i<h, a+(i:ZMod p)≠0) (C : ℝ) (hC : 0≤C)
    (huniv : ∀ W : ℕ → ℕ → ℝ, (∀ i<h, ∀ j<h, 0≤W i j ∧ W i j≤1) →
      matrixEnergy h W a ≤ C*matrixMass h W) : (h:ℝ)≤8*C := by
  have he := huniv (alignedMatrix a) (by
    intro i hi j hj
    rcases alignedMatrix_zero_one h a ha i j hi hj with he | he <;> simp [he])
  have hu := mul_le_mul_of_nonneg_left (alignedMatrix_mass_le h a ha) hC
  have hl := alignedMatrix_energy_lower h a ha
  have hsq : (0:ℝ)<(h:ℝ)^2 := by positivity
  apply le_of_mul_le_mul_right (a := (h:ℝ)^2) _ hsq
  nlinarith only [he,hu,hl]

end Erdos66AdaptiveMatrixEnergy
