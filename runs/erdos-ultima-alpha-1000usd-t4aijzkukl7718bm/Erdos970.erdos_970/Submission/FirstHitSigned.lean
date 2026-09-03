import Submission.FirstHitSharpCost

/-! A first-hit lower sieve using arbitrary signed orthogonal kernels.
The displayed quantitative hypothesis is essential and is not asserted uniformly. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma linearKernel_eq_sum_of_avoids_support (q : ι → ℝ) (c : Finset ι → ℝ)
    (ω : ι → Bool) (hω : ∀ Q, c Q ≠ 0 → ∀ i ∈ Q, ω i = false) :
    linearKernel q c ω = ∑ Q : Finset ι, c Q := by
  apply sum_congr rfl
  intro Q hQ
  by_cases hc : c Q = 0
  · simp [hc]
  · have hb : basis q Q ω = 1 := by
      rw [basis_eq_prod]
      apply prod_eq_one
      intro i hi
      simp [contrast, hω Q hc i hi]
    rw [hb, mul_one]

/-- Signed kernels supported off a coordinate are independent of its hit. -/
lemma linearKernel_hit_average_of_not_mem (q : ι → ℝ) (hq : ∀ i, q i ≠ 0)
    (c : Finset ι → ℝ) (i : ι) (hc : ∀ Q, i ∈ Q → c Q = 0) :
    average q (fun ω => hitMonomial {i} ω * linearKernel q c ω ^ 2) =
      q i * (∑ Q : Finset ι, c Q ^ 2 * variance q Q) := by
  have hmono (ω : ι → Bool) : hitMonomial {i} ω = hitCoordinate i ω := by
    simp only [hitMonomial, prod_singleton, hitCoordinate]
  simp_rw [hmono]
  rw [linearKernel_hit_average q hq c i]
  congr 1
  rw [sum_all_split i (fun Q => c Q ^ 2 * variance q Q)]
  apply sum_congr rfl
  intro Q hQ
  rw [hc (insert i Q) (mem_insert_self i Q)]
  ring

section Ordered
variable [LinearOrder ι]

/-- The first nonzero hit has a normalized kernel equal to one, regardless of
signs among its orthogonal coefficients. -/
theorem first_hit_signed_sum_ge_one (q : ι → ℝ) (c : ι → Finset ι → ℝ)
    (hsum : ∀ i, (∑ Q : Finset ι, c i Q) = 1)
    (hprior : ∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i)
    (ω : ι → Bool) (hω : ω ≠ (fun _ => false)) :
    1 ≤ ∑ i, hitMonomial {i} ω * linearKernel q (c i) ω ^ 2 := by
  classical
  let B := univ.filter (fun i => ω i = true)
  have hBn : B.Nonempty := by
    by_contra h
    apply hω
    funext i
    cases hi : ω i
    · rfl
    · exact False.elim (h ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩)
  let i := B.min' hBn
  have hi : ω i = true := (mem_filter.mp (B.min'_mem hBn)).2
  have hj (j : ι) (hji : j < i) : ω j = false := by
    cases he : ω j
    · rfl
    · have hle : i ≤ j := B.min'_le j (mem_filter.mpr ⟨mem_univ j, he⟩)
      exact False.elim ((not_lt_of_ge hle) hji)
  have hk : linearKernel q (c i) ω = 1 := by
    rw [linearKernel_eq_sum_of_avoids_support q (c i) ω
      (fun Q hQ j hjQ => hj j (hprior i Q hQ j hjQ)), hsum i]
  have hnonneg (j : ι) : 0 ≤ hitMonomial {j} ω * linearKernel q (c j) ω ^ 2 := by
    apply mul_nonneg _ (sq_nonneg _)
    simp only [hitMonomial, prod_singleton]
    split_ifs <;> norm_num
  have hh := single_le_sum (s := univ)
    (f := fun j => hitMonomial {j} ω * linearKernel q (c j) ω ^ 2)
    (fun j _ => hnonneg j) (mem_univ i)
  simpa [hitMonomial, hi, hk] using hh

/-- A first-hit survivor criterion with arbitrary signed kernels and their exact
ordinary-coefficient costs. The sum of mean-plus-cost objectives must be < m. -/
theorem survivor_of_first_hit_signed (q : ι → ℝ) (hq : ∀ i, q i ≠ 0)
    (c : ι → Finset ι → ℝ)
    (hsum : ∀ i, (∑ Q : Finset ι, c i Q) = 1)
    (hprior : ∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i)
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1)
    (hmain : (∑ i, ((m : ℝ) * q i * (∑ Q : Finset ι, c i Q ^ 2 * variance q Q) +
        kernelCost q (c i) ^ 2)) < m) :
    ∃ j < m, ∀ i, ω j i = false := by
  classical
  by_contra hbad
  push_neg at hbad
  have hlower : (m : ℝ) ≤ ∑ j ∈ range m,
      ∑ i, hitMonomial {i} (ω j) * linearKernel q (c i) (ω j) ^ 2 := by
    calc
      _ = ∑ j ∈ range m, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro j hj
        apply first_hit_signed_sum_ge_one q c hsum hprior (ω j)
        intro heq
        obtain ⟨i, hi⟩ := hbad j (mem_range.mp hj)
        exact hi (congrFun heq i)
  have hbound (i : ι) :
      (∑ j ∈ range m, hitMonomial {i} (ω j) * linearKernel q (c i) (ω j) ^ 2) ≤
        (m : ℝ) * q i * (∑ Q : Finset ι, c i Q ^ 2 * variance q Q) +
          kernelCost q (c i) ^ 2 := by
    have he := arbitrary_square_hit_error q (c i) m ω herr {i}
    have hnot (Q : Finset ι) (hiQ : i ∈ Q) : c i Q = 0 := by
      by_contra hc
      exact lt_irrefl i (hprior i Q hc i hiQ)
    rw [linearKernel_hit_average_of_not_mem q hq (c i) i hnot] at he
    linarith [(abs_le.mp he).2]
  rw [sum_comm] at hlower
  have hupper := sum_le_sum (s := univ) (fun i _ => hbound i)
  exact hmain.not_ge (hlower.trans hupper)

end Ordered
#print axioms linearKernel_hit_average_of_not_mem
#print axioms survivor_of_first_hit_signed
end Erdos970.FiniteSelberg
