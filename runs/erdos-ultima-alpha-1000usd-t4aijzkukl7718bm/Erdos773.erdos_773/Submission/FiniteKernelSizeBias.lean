import Submission.FiniteKernelCrossing

/-!
Nonnegative size-biasing of a finite transition kernel. Zero normalizers
fall back to the original kernel. At a positive normalizer, the tilted law
has precisely the intended weighted conditional averages and support.
-/
namespace Erdos773.FiniteKernelSizeBias
open Finset FiniteKernelCrossing
set_option maxHeartbeats 2500000
noncomputable section
variable {σ : Type*} [Fintype σ]

/-- Size-bias a finite kernel; do not divide by a zero normalizer. -/
def tilt (K : Kernel σ) (f : σ → ℝ) (hf : ∀ x, 0 ≤ f x) : Kernel σ where
  weight x y := by
    classical
    exact if 0 < K.avg f x then K.weight x y*f y/K.avg f x else K.weight x y
  nonneg x y := by
    classical
    split_ifs with h
    · exact div_nonneg (mul_nonneg (K.nonneg x y) (hf y)) h.le
    · exact K.nonneg x y
  total x := by
    classical
    by_cases h : 0 < K.avg f x
    · simp only [if_pos h, ← sum_div]
      exact div_self h.ne'
    · simpa only [if_neg h] using K.total x

/-- Exact tilted average at a positive normalizer. -/
theorem avg_tilt (K : Kernel σ) (f : σ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (g : σ → ℝ) (x : σ) (hZ : 0 < K.avg f x) :
    (tilt K f hf).avg g x = K.avg (fun y => f y*g y) x/K.avg f x := by
  classical
  change 0 < (∑ y, K.weight x y*f y) at hZ
  simp only [Kernel.avg, tilt, if_pos hZ, div_mul_eq_mul_div, ← sum_div, mul_assoc]

theorem avg_tilt_zero (K : Kernel σ) (f : σ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (g : σ → ℝ) (x : σ) (hZ : ¬0 < K.avg f x) :
    (tilt K f hf).avg g x = K.avg g x := by
  classical
  change ¬0 < (∑ y, K.weight x y*f y) at hZ
  simp only [Kernel.avg, tilt, if_neg hZ]

/-- Tilting cannot introduce an unsupported transition. When the normalizer
is positive, destinations with zero weight f are excluded exactly. -/
theorem support_tilt (K : Kernel σ) (f : σ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (x y : σ) (hZ : 0 < K.avg f x) :
    0 < (tilt K f hf).weight x y ↔ 0 < K.weight x y ∧ 0 < f y := by
  classical
  change 0 < (if 0 < K.avg f x then K.weight x y*f y/K.avg f x else K.weight x y) ↔ _
  rw [if_pos hZ, div_pos_iff_of_pos_right hZ]
  rw [mul_pos_iff]
  constructor
  · rintro (h | h)
    · exact h
    · have hh := K.nonneg x y
      linarith only [hh, h.1]
  · exact Or.inl

lemma avg_sub (K : Kernel σ) (f g : σ → ℝ) (x : σ) :
    K.avg (fun y => f y-g y) x = K.avg f x-K.avg g x := by
  simp only [Kernel.avg, mul_sub, sum_sub_distrib]

/-- Centering a finite conditional second moment at its actual mean. -/
lemma variance_identity (K : Kernel σ) (f : σ → ℝ) (x : σ) :
    K.avg (fun y => (f y-K.avg f x)^2) x = K.avg (fun y => (f y)^2) x-(K.avg f x)^2 := by
  have he (y : σ) : (f y-K.avg f x)^2 = (f y)^2-2*K.avg f x*f y+(K.avg f x)^2 := by ring
  simp_rw [he]
  rw [Kernel.avg_add, avg_sub, Kernel.avg_mul, Kernel.avg_const]
  ring

/-- Size-bias favors larger values by exactly variance/mean. This is an
identity, rather than an independence assertion or an omitted correction. -/
theorem tilt_mean (K : Kernel σ) (f : σ → ℝ) (hf : ∀ y, 0 ≤ f y)
    (x : σ) (hZ : 0 < K.avg f x) :
    (tilt K f hf).avg f x = K.avg f x+
      K.avg (fun y => (f y-K.avg f x)^2) x/K.avg f x := by
  rw [avg_tilt K f hf f x hZ, variance_identity]
  have he : (fun y => f y*f y) = (fun y => (f y)^2) := by funext y; ring
  rw [he]
  field_simp
  ring

/-- For remaining volume f and current volume Q, the mean decrement is
improved by the same favorable variance term. -/
theorem tilt_decrement (K : Kernel σ) (f : σ → ℝ) (hf : ∀ y, 0 ≤ f y)
    (x : σ) (Q : ℝ) (hZ : 0 < K.avg f x) :
    (tilt K f hf).avg (fun y => f y-Q) x =
      -(Q-K.avg f x)+K.avg (fun y => (f y-K.avg f x)^2) x/K.avg f x := by
  rw [avg_sub, Kernel.avg_const, tilt_mean K f hf x hZ]
  ring

/-- Nonnegative observables have a direct comparison with the original
kernel when f has an upper support bound. -/
theorem avg_tilt_le (K : Kernel σ) (f : σ → ℝ) (hf : ∀ y, 0 ≤ f y)
    (g : σ → ℝ) (hg : ∀ y, 0 ≤ g y) (x : σ) (M : ℝ)
    (hM : ∀ y, 0 < K.weight x y → f y ≤ M) (hZ : 0 < K.avg f x) :
    (tilt K f hf).avg g x ≤ M*K.avg g x/K.avg f x := by
  rw [avg_tilt K f hf g x hZ]
  apply div_le_div_of_nonneg_right _ hZ.le
  have hh := K.avg_mono_support x (fun y hy => mul_le_mul_of_nonneg_right (hM y hy) (hg y))
  simpa only [Kernel.avg_mul] using hh

#print axioms tilt
#print axioms avg_tilt
#print axioms support_tilt
#print axioms variance_identity
#print axioms tilt_mean
#print axioms tilt_decrement
#print axioms avg_tilt_le
end
end Erdos773.FiniteKernelSizeBias
