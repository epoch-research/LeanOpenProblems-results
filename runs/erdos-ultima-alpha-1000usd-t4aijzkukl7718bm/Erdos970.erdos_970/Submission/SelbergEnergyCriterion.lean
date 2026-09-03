import Submission.SelbergEnergy

/-! A quantitative survivor criterion for arbitrary Selberg lower kernels. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def ordinaryCoefficient (q : ι → ℝ) (c : Finset ι → ℝ) (T : Finset ι) : ℝ :=
  (-1) ^ T.card / (∏ i ∈ T, q i) * ∑ Q : Finset ι, if T ⊆ Q then c Q else 0

lemma linearKernel_expansion (q : ι → ℝ) (c : Finset ι → ℝ) (ω : ι → Bool) :
    linearKernel q c ω = ∑ T : Finset ι, ordinaryCoefficient q c T * hitMonomial T ω := by
  classical
  simp only [linearKernel, basis_expansion, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  simp only [ordinaryCoefficient, mul_sum, sum_mul]
  apply sum_congr rfl
  intro Q hQ
  split_ifs <;> ring

noncomputable def kernelCost (q : ι → ℝ) (c : Finset ι → ℝ) : ℝ :=
  ∑ T : Finset ι, |ordinaryCoefficient q c T|

lemma arbitrary_square_hit_error (q : ι → ℝ) (c : Finset ι → ℝ)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (U : Finset ι) :
    |(∑ j ∈ range m, hitMonomial U (ω j) * linearKernel q c (ω j) ^ 2) -
      (m : ℝ) * average q (fun v => hitMonomial U v * linearKernel q c v ^ 2)| ≤
      kernelCost q c ^ 2 := by
  have heq (v : ι → Bool) : hitMonomial U v * linearKernel q c v ^ 2 =
      ∑ a ∈ (univ : Finset (Finset ι)) ×ˢ univ,
        (ordinaryCoefficient q c a.1 * ordinaryCoefficient q c a.2) *
          hitMonomial (U ∪ (a.1 ∪ a.2)) v := by
    rw [linearKernel_expansion, pow_two, sum_mul_sum, sum_product, mul_sum]
    apply sum_congr rfl
    intro Q hQ
    rw [mul_sum]
    apply sum_congr rfl
    intro R hR
    rw [← hitMonomial_mul, ← hitMonomial_mul]
    ring
  simp_rw [heq]
  apply (finite_polynomial_interval_error _ _ _ q m ω herr).trans_eq
  simp only [sum_product, abs_mul, kernelCost, pow_two, sum_mul_sum]

lemma hit_sum_one_le_of_nonempty (ω : ι → Bool) (hω : ω ≠ fun _ => false) :
    1 ≤ ∑ i, hitCoordinate i ω := by
  have hex : ∃ i, ω i = true := by
    by_contra h
    apply hω
    funext i
    have hi : ω i ≠ true := by intro hi; exact h ⟨i, hi⟩
    cases hωi : ω i <;> simp_all
  obtain ⟨i, hi⟩ := hex
  have h := single_le_sum (s := univ) (f := fun i => hitCoordinate i ω)
    (fun j _ => by simp only [hitCoordinate]; split_ifs <;> norm_num) (mem_univ i)
  simpa [hitCoordinate, hi] using h

lemma lowerKernel_nonpos_of_nonempty (q : ι → ℝ) (c : Finset ι → ℝ)
    (ω : ι → Bool) (hω : ω ≠ fun _ => false) :
    (1 - ∑ i, hitCoordinate i ω) * linearKernel q c ω ^ 2 ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hit_sum_one_le_of_nonempty ω hω)) (sq_nonneg _)

/-- The remainder for an arbitrary squared lower kernel depends on the L1 norm of its
ordinary coefficients, not on the mere number of supported divisors. -/
theorem arbitrary_lowerKernel_error (q : ι → ℝ) (hq : ∀ i, q i ≠ 0)
    (c : Finset ι → ℝ) (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1) :
    |(∑ j ∈ range m, (1 - ∑ i, hitCoordinate i (ω j)) * linearKernel q c (ω j) ^ 2) -
      (m : ℝ) * kernelEnergy q c| ≤ (Fintype.card ι + 1 : ℝ) * kernelCost q c ^ 2 := by
  let E (U : Finset ι) :=
    (∑ j ∈ range m, hitMonomial U (ω j) * linearKernel q c (ω j) ^ 2) -
      (m : ℝ) * average q (fun v => hitMonomial U v * linearKernel q c v ^ 2)
  have hE (U : Finset ι) : |E U| ≤ kernelCost q c ^ 2 := arbitrary_square_hit_error q c m ω herr U
  have heq (v : ι → Bool) : (1 - ∑ i, hitCoordinate i v) * linearKernel q c v ^ 2 =
      hitMonomial ∅ v * linearKernel q c v ^ 2 - ∑ i, hitMonomial {i} v * linearKernel q c v ^ 2 := by
    simp only [hitMonomial, prod_empty, prod_singleton, hitCoordinate]
    rw [← sum_mul]
    ring
  have hsplit : (∑ j ∈ range m, (1 - ∑ i, hitCoordinate i (ω j)) * linearKernel q c (ω j) ^ 2) -
      (m : ℝ) * kernelEnergy q c = E ∅ - ∑ i, E {i} := by
    rw [← lowerKernel_average q hq c]
    simp_rw [heq]
    rw [average_sub, average_sum]
    simp only [E, sum_sub_distrib, mul_sum, mul_sub]
    rw [sum_comm]
    ring
  rw [hsplit]
  calc
    _ ≤ |E ∅| + |∑ i, E {i}| := abs_sub _ _
    _ ≤ kernelCost q c ^ 2 + ∑ i, |E {i}| := add_le_add (hE ∅) (abs_sum_le_sum_abs _ _)
    _ ≤ kernelCost q c ^ 2 + ∑ i : ι, kernelCost q c ^ 2 :=
      add_le_add le_rfl (sum_le_sum (fun i _ => hE {i}))
    _ = _ := by simp; ring

/-- A sufficient condition for a survivor, with the energy and coefficient cost both explicit.
This theorem does not assert that the condition holds uniformly for m=C*k^2. -/
theorem survivor_of_kernelEnergy (q : ι → ℝ) (hq : ∀ i, q i ≠ 0)
    (c : Finset ι → ℝ) (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (hmain : (Fintype.card ι + 1 : ℝ) * kernelCost q c ^ 2 < (m : ℝ) * kernelEnergy q c) :
    ∃ j < m, ∀ i, ω j i = false := by
  by_contra hbad
  push_neg at hbad
  have hsum : (∑ j ∈ range m,
      (1 - ∑ i, hitCoordinate i (ω j)) * linearKernel q c (ω j) ^ 2) ≤ 0 := by
    apply sum_nonpos
    intro j hj
    apply lowerKernel_nonpos_of_nonempty
    intro he
    obtain ⟨i, hi⟩ := hbad j (mem_range.mp hj)
    exact hi (congrFun he i)
  have h := (abs_le.mp (arbitrary_lowerKernel_error q hq c m ω herr)).1
  linarith

#print axioms survivor_of_kernelEnergy
end Erdos970.FiniteSelberg
