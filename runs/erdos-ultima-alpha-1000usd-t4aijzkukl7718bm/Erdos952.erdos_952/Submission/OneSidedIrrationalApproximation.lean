import Submission.IrrationalLatticeApproximation

/-! One-sided approximation by points of a translated period lattice. -/
namespace Erdos952Investigation
namespace IrrationalLatticeApproximation

set_option maxHeartbeats 0

lemma arbitrarily_large_period_vector {α : ℝ} (hα : Irrational α)
    (P M : ℤ) (hP : 0 < P) :
    ∃ k l : ℤ, M < P*k ∧
      |α*((P*k : ℤ) : ℝ)-((P*l : ℤ) : ℝ)| < 1/2 := by
  obtain ⟨k,l,hfar,hnear⟩ := arbitrarily_far_grid_center hα 0 (2*P)
    (2*|M|+2) (by omega)
  have hfar' : |M|+1 < |P*k| := by
    have he : |(2*P)*k| = 2*|P*k| := by rw [mul_assoc, abs_mul]; norm_num
    simp only [zero_add, he] at hfar
    omega
  have hnear' : |α*((P*k : ℤ) : ℝ)-((P*l : ℤ) : ℝ)| < 1/2 := by
    have he : α*((0+(2*P)*k : ℤ) : ℝ)-(((2*P)*l : ℤ) : ℝ) =
        2*(α*((P*k : ℤ) : ℝ)-((P*l : ℤ) : ℝ)) := by push_cast; ring
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hnear
    linarith
  by_cases hk : 0 ≤ P*k
  · refine ⟨k,l,?_,hnear'⟩
    rw [abs_of_nonneg hk] at hfar'
    have := le_abs_self M
    omega
  · refine ⟨-k,-l,?_,?_⟩
    · rw [abs_of_neg (lt_of_not_ge hk)] at hfar'
      have := le_abs_self M
      simp only [mul_neg]
      omega
    · have he : α*((P* -k : ℤ) : ℝ)-((P* -l : ℤ) : ℝ) =
          -(α*((P*k : ℤ) : ℝ)-((P*l : ℤ) : ℝ)) := by push_cast; ring
      rw [he, abs_neg]
      exact hnear'

lemma arbitrarily_large_affine_grid_center {α : ℝ} (hα : Irrational α)
    (A P M : ℤ) (β : ℝ) (hP : 0 < P) :
    ∃ k l : ℤ, M < A+P*k ∧
      |α*((A+P*k : ℤ) : ℝ)-((P*l : ℤ) : ℝ)-β| < 1 := by
  obtain ⟨⟨k₀,l₀⟩,hy⟩ :=
    (dense_affine_grid hα A P hP.ne').exists_mem_open isOpen_Ioo
      (Set.nonempty_Ioo.mpr (by linarith : β-1/2 < β+1/2))
  have hnear₀ : |α*((A+P*k₀ : ℤ) : ℝ)-((P*l₀ : ℤ) : ℝ)-β| < 1/2 := by
    simp only [Int.cast_add, Int.cast_mul]
    exact abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨k₁,l₁,hfar,hnear₁⟩ := arbitrarily_large_period_vector hα P (M-(A+P*k₀)) hP
  refine ⟨k₀+k₁,l₀+l₁,?_,?_⟩
  · nlinarith
  · have he : α*((A+P*(k₀+k₁) : ℤ) : ℝ)-((P*(l₀+l₁) : ℤ) : ℝ)-β =
        (α*((A+P*k₀ : ℤ) : ℝ)-((P*l₀ : ℤ) : ℝ)-β) +
          (α*((P*k₁ : ℤ) : ℝ)-((P*l₁ : ℤ) : ℝ)) := by push_cast; ring
    rw [he]
    exact (abs_add_le _ _).trans_lt (by linarith)

#print axioms arbitrarily_large_affine_grid_center

end IrrationalLatticeApproximation
end Erdos952Investigation
