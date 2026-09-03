import Submission.FirstHitBooleanCost

/-! For prior-supported first-hit kernels, different first-hit indices produce
disjoint monomial supports. Thus there is no further cancellation between their
already Boolean-reduced coefficient lists. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

lemma ordinaryCoefficient_prior (q : ι → ℝ) (c : ι → Finset ι → ℝ)
    (hc : ∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i) (i : ι) :
    ∀ T, ordinaryCoefficient q (c i) T ≠ 0 → ∀ j ∈ T, j < i := by
  intro T hT j hj
  by_contra hjbad
  apply hT
  unfold ordinaryCoefficient
  have hz : (∑ Q : Finset ι, if T ⊆ Q then c i Q else 0) = 0 := by
    apply sum_eq_zero
    intro Q hQ
    by_cases hTQ : T ⊆ Q
    · have hzero : c i Q = 0 := by
        by_contra hn
        exact hjbad (hc i Q hn j (hTQ hj))
      simp [hzero]
    · simp [hTQ]
  rw [hz, mul_zero]

lemma booleanSquareCoefficient_prior (a : Finset ι → ℝ) (i : ι)
    (ha : ∀ Q, a Q ≠ 0 → ∀ j ∈ Q, j < i) :
    ∀ T, booleanSquareCoefficient a T ≠ 0 → ∀ j ∈ T, j < i := by
  intro T hT j hj
  obtain ⟨Q, _, hQ⟩ := exists_ne_zero_of_sum_ne_zero hT
  obtain ⟨R, _, hR⟩ := exists_ne_zero_of_sum_ne_zero hQ
  by_cases he : Q ∪ R = T
  · rw [if_pos he] at hR
    obtain ⟨haQ, haR⟩ := mul_ne_zero_iff.mp hR
    rw [← he, mem_union] at hj
    rcases hj with hj | hj
    · exact ha Q haQ j hj
    · exact ha R haR j hj
  · simp [he] at hR

/-- Coefficients after multiplying a polynomial supported off `i` by its hit. -/
noncomputable def hitShiftCoefficient (i : ι) (b : Finset ι → ℝ) (T : Finset ι) : ℝ :=
  if i ∈ T then b (T.erase i) else 0

omit [LinearOrder ι] in
lemma hitShift_expansion (i : ι) (b : Finset ι → ℝ)
    (hb : ∀ T, i ∈ T → b T = 0) (ω : ι → Bool) :
    (∑ T : Finset ι, hitShiftCoefficient i b T * hitMonomial T ω) =
      hitMonomial {i} ω * (∑ T : Finset ι, b T * hitMonomial T ω) := by
  rw [sum_all_split i, sum_all_split i (fun T => b T * hitMonomial T ω), mul_sum]
  apply sum_congr rfl
  intro Q hQ
  have hiQ := not_mem_of_erase_powerset hQ
  simp only [hitShiftCoefficient, if_neg hiQ, mem_insert_self, if_true,
    erase_insert hiQ, hb (insert i Q) (mem_insert_self _ _), zero_mul, zero_add, add_zero]
  rw [show insert i Q = {i} ∪ Q by simp, ← hitMonomial_mul]
  ring

omit [LinearOrder ι] in
lemma hitShift_cost (i : ι) (b : Finset ι → ℝ)
    (hb : ∀ T, i ∈ T → b T = 0) :
    (∑ T : Finset ι, |hitShiftCoefficient i b T|) = ∑ T : Finset ι, |b T| := by
  rw [sum_all_split i, sum_all_split i (fun T => |b T|)]
  apply sum_congr rfl
  intro Q hQ
  have hiQ := not_mem_of_erase_powerset hQ
  simp [hitShiftCoefficient, hiQ, hb (insert i Q) (mem_insert_self _ _)]

omit [Fintype ι] in
lemma hitShift_max (i : ι) (b : Finset ι → ℝ)
    (hb : ∀ T, b T ≠ 0 → ∀ j ∈ T, j < i)
    (T : Finset ι) (hT : hitShiftCoefficient i b T ≠ 0) :
    i ∈ T ∧ ∀ j ∈ T, j ≤ i := by
  by_cases hi : i ∈ T
  · refine ⟨hi, ?_⟩
    have hne : b (T.erase i) ≠ 0 := by simpa [hitShiftCoefficient, hi] using hT
    intro j hj
    by_cases hji : j = i
    · exact hji.le
    · exact (hb _ hne j (mem_erase.mpr ⟨hji, hj⟩)).le
  · simp [hitShiftCoefficient, hi] at hT

omit [Fintype ι] in
/-- Distinct first-hit indices cannot contribute to the same monomial. -/
lemma hitShift_disjoint (b : ι → Finset ι → ℝ)
    (hb : ∀ i T, b i T ≠ 0 → ∀ j ∈ T, j < i)
    (i j : ι) (hij : i ≠ j) (T : Finset ι) :
    hitShiftCoefficient i (b i) T = 0 ∨ hitShiftCoefficient j (b j) T = 0 := by
  by_contra hbad
  push_neg at hbad
  have hi := hitShift_max i (b i) (hb i) T hbad.1
  have hj := hitShift_max j (b j) (hb j) T hbad.2
  exact hij (le_antisymm (hj.2 i hi.1) (hi.2 j hj.1))

/-- Combining all first-hit lists gives exactly their summed L1 costs. -/
theorem firstHit_merged_cost (b : ι → Finset ι → ℝ)
    (hb : ∀ i T, b i T ≠ 0 → ∀ j ∈ T, j < i) :
    (∑ T : Finset ι, |∑ i, hitShiftCoefficient i (b i) T|) =
      ∑ i, ∑ T : Finset ι, |b i T| := by
  calc
    _ = ∑ T : Finset ι, ∑ i, |hitShiftCoefficient i (b i) T| := by
      apply sum_congr rfl
      intro T hT
      by_cases hn : ∃ i, hitShiftCoefficient i (b i) T ≠ 0
      · obtain ⟨i, hi⟩ := hn
        have hz (j : ι) (hj : j ≠ i) : hitShiftCoefficient j (b j) T = 0 :=
          (hitShift_disjoint b hb j i hj T).resolve_right hi
        rw [sum_eq_single i (fun j _ hj => hz j hj) (by simp),
          sum_eq_single i (fun j _ hj => by rw [hz j hj, abs_zero]) (by simp)]
      · push_neg at hn
        simp [hn]
    _ = ∑ i, ∑ T : Finset ι, |hitShiftCoefficient i (b i) T| := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      apply hitShift_cost
      intro T hiT
      by_contra hn
      exact lt_irrefl i (hb i T hn i hiT)

/-- In particular, no cross-index saving was lost by the Boolean first-hit criterion. -/
theorem firstHit_boolean_merged_cost (q : ι → ℝ) (c : ι → Finset ι → ℝ)
    (hc : ∀ i Q, c i Q ≠ 0 → ∀ j ∈ Q, j < i) :
    (∑ T : Finset ι, |∑ i, hitShiftCoefficient i
        (booleanSquareCoefficient (ordinaryCoefficient q (c i))) T|) =
      ∑ i, booleanSquareCost (ordinaryCoefficient q (c i)) := by
  apply firstHit_merged_cost
  intro i
  exact booleanSquareCoefficient_prior _ i (ordinaryCoefficient_prior q c hc i)

#print axioms firstHit_boolean_merged_cost
end Erdos970.FiniteSelberg
