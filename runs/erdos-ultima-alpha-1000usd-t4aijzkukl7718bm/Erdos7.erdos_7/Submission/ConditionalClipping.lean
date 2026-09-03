import FormalConjecturesUtil

/-!
# Conditional backward clipping

Auxiliary finite-measure inequalities. These do not prove any arithmetic
covering obstruction or any joint geometric comparison theorem.
-/
namespace Erdos7ConditionalClipping
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- Unlike a constant clipping threshold, a threshold depending on the old
coordinate requires a fiberwise mass identity. The comparison hypothesis is
explicit: it is not implied by scalar bounds on unrelated test families. -/
theorem fiber_clipped_step {Ω A : Type*} [Fintype Ω] [Fintype A]
    (μ : Ω → ℚ) (ν : Ω → A → ℚ) (hν : ∀ x y, 0 ≤ ν x y)
    (F : Ω → A → ℚ) (D ell loss T : Ω → ℚ)
    (hell : ∀ x, ell x ≤ 1)
    (hmass : ∀ x, (∑ y, ν x y) = μ x - D x)
    (hfuture : (∑ x, ∑ y, ν x y) ≤ ∑ x, ∑ y, ν x y * F x y)
    (hloss : ∀ x, D x ≤ μ x * loss x)
    (hcomparison : (∑ x, ∑ y, ν x y * max (F x y - ell x) 0) ≤
      ∑ x, μ x * T x) :
    (∑ x, μ x) ≤ ∑ x, μ x * (ell x + (1 - ell x) * loss x + T x) := by
  have hclip : (∑ x, ∑ y, ν x y * F x y) ≤
      (∑ x, (μ x - D x) * ell x) + ∑ x, μ x * T x := by
    calc
      _ ≤ ∑ x, ∑ y, ν x y * (ell x + max (F x y - ell x) 0) := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_of_nonneg_left _ (hν x y)
        have hh := le_max_left (F x y - ell x) (0 : ℚ)
        linarith
      _ = (∑ x, (μ x - D x) * ell x) +
          ∑ x, ∑ y, ν x y * max (F x y - ell x) 0 := by
        simp only [mul_add, Finset.sum_add_distrib]
        simp_rw [← Finset.sum_mul, hmass]
      _ ≤ _ := add_le_add le_rfl hcomparison
  have hmain := hfuture.trans hclip
  simp_rw [hmass] at hmain
  have hbound : (∑ x, (μ x - D x) * ell x) +
        (∑ x, μ x * T x) + (∑ x, D x) ≤
      ∑ x, μ x * (ell x + (1 - ell x) * loss x + T x) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    have hh := mul_le_mul_of_nonneg_left (hloss x) (sub_nonneg.mpr (hell x))
    nlinarith
  have hid : (∑ x, (μ x - D x)) = (∑ x, μ x) - ∑ x, D x :=
    Finset.sum_sub_distrib μ D
  rw [hid] at hmain
  linarith

/-- The usual retained-mass formula for a cap `c` and a target retention `h`.
This algebraic identity allows either control to depend on the old point. -/
theorem retention_defect (c h alpha : ℚ) :
    1 - min h (c * (1 - alpha)) = max (1 - h) (1 - c * (1 - alpha)) := by
  by_cases hh : h ≤ c * (1 - alpha)
  · rw [min_eq_left hh, max_eq_left (by linarith)]
  · rw [min_eq_right (le_of_not_ge hh), max_eq_right (by linarith)]

/-- Positive coefficients preserve the direction of the pointwise loss bound,
even when the clipping threshold is history dependent. -/
theorem conditional_loss_bound (mu D ell loss : ℚ)
    (hell : ell ≤ 1) (hD : D ≤ mu * loss) :
    mu * ell + (1 - ell) * D ≤ mu * (ell + (1 - ell) * loss) := by
  have hh := mul_le_mul_of_nonneg_left hD (sub_nonneg.mpr hell)
  nlinarith

#print axioms fiber_clipped_step
#print axioms retention_defect
#print axioms conditional_loss_bound

/-- A smaller offset is paired with a larger future value in the maximizing
uncrossing of two pairs. This is the elementary Monge inequality relevant to
history-dependent clipping. -/
theorem clipped_monge (u v a b : ℚ) (huv : u ≤ v) (hab : a ≤ b) :
    max (u - a) 0 + max (v - b) 0 ≤
      max (u - b) 0 + max (v - a) 0 := by
  simp only [max_def]
  split_ifs <;> linarith

/-- A nonnegative mixture of clipped monotone tests has the same uncrossing
orientation. This finite inequality alone does not supply a transport theorem
for arbitrary families of random variables. -/
theorem mixture_clipped_monge {ι α : Type*} [Preorder α]
    (S : Finset ι) (w : ι → ℚ) (F : ι → α → ℚ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hF : ∀ i ∈ S, Monotone (F i))
    (x y : α) (hxy : x ≤ y) (a b : ℚ) (hab : a ≤ b) :
    (∑ i ∈ S, w i * max (F i x - a) 0) +
        (∑ i ∈ S, w i * max (F i y - b) 0) ≤
      (∑ i ∈ S, w i * max (F i x - b) 0) +
        (∑ i ∈ S, w i * max (F i y - a) 0) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [mul_add] using mul_le_mul_of_nonneg_left
    (clipped_monge (F i x) (F i y) a b (hF i hi hxy) hab) (hw i hi)

#print axioms clipped_monge
#print axioms mixture_clipped_monge
end Erdos7ConditionalClipping
