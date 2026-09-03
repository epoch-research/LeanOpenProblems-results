import Submission.BinaryCriticalGeneralObserver

/-! A signed-observer lower bound allowing a uniformly bounded error in all
noncritical coordinates. No concrete global certificate is asserted. -/
namespace Erdos406BoundedErrorObserver
open scoped Matrix BigOperators

lemma dot_error_bound {ι : Type*} [Fintype ι]
    (u e D : ι → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (he : ∀ i, |e i| ≤ D i * t) :
    |u ⬝ᵥ e| ≤ (∑ i, |u i| * D i) * t := by
  calc
    |u ⬝ᵥ e| ≤ ∑ i, |u i * e i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |u i| * |e i| := by simp only [abs_mul]
    _ ≤ ∑ i, (|u i| * D i) * t := by
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_left (he i) (abs_nonneg (u i))
      simpa only [mul_assoc] using h
    _ = (∑ i, |u i| * D i) * t := by rw [Finset.sum_mul]

lemma critical_lower {ι : Type*} [Fintype ι]
    (u a e v D : ι → ℝ) (γ t : ℝ) (k : ℕ)
    (hγ : 0 ≤ γ) (ht : 0 ≤ t) (hua : 1 ≤ u ⬝ᵥ a)
    (hv : v = (γ*k*t) • a + e) (he : ∀ i, |e i| ≤ D i * t) :
    γ*k*t ≤ u ⬝ᵥ v + (∑ i, |u i| * D i) * t := by
  have hb := dot_error_bound u e D t ht he
  have ha := mul_le_mul_of_nonneg_left hua
    (by positivity : 0 ≤ γ*(k:ℝ)*t)
  have hab := neg_abs_le (u ⬝ᵥ e)
  rw [hv, dotProduct_add, dotProduct_smul, smul_eq_mul]
  nlinarith

#print axioms dot_error_bound
#print axioms critical_lower
end Erdos406BoundedErrorObserver
