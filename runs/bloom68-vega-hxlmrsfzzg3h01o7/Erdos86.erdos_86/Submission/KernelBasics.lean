import FormalConjecturesUtil

/-!
Finite-type consequences of the kernel support inequality.
These lemmas do not assert that an arbitrary cube graph admits such a kernel.
They are supporting results only, not a proof of Erdős 86.
-/

namespace Erdos86.KernelBasics

open scoped BigOperators

/-- The pointwise support condition forces every symmetric kernel entry to be at most half. -/
theorem kernel_le_half {α : Type*} (W : α → α → ℝ)
    (hsymm : ∀ a b, W a b = W b a)
    (hsupport : ∀ a b c d, 0 < W a b → 0 < W c d → W a c + W b d ≤ 1) :
    ∀ a b, W a b ≤ 1 / 2 := by
  intro a b
  by_cases hab : 0 < W a b
  · have hba : 0 < W b a := by simpa only [hsymm b a] using hab
    have h := hsupport a b b a hab hba
    rw [hsymm b a] at h
    linarith
  · linarith

/-- Every finite probability-weighted average of such a kernel is at most half. -/
theorem weighted_kernel_le_half {α : Type*} [Fintype α]
    (W : α → α → ℝ) (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1)
    (hsymm : ∀ a b, W a b = W b a)
    (hsupport : ∀ a b c d, 0 < W a b → 0 < W c d → W a c + W b d ≤ 1) :
    (∑ a, ∑ b, w a * w b * W a b) ≤ 1 / 2 := by
  calc
    (∑ a, ∑ b, w a * w b * W a b) ≤
        ∑ a, ∑ b, w a * w b * (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (kernel_le_half W hsymm hsupport a b)
        (mul_nonneg (hw a) (hw b))
    _ = 1 / 2 := by
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      norm_num [hsum]

end Erdos86.KernelBasics
