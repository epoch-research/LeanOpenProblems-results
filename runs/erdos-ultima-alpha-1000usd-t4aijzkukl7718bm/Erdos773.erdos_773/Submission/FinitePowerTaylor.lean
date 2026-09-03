import Submission.FiniteKernelCrossing

/-!
Natural-power Taylor bounds and finite-kernel moment transfer. The remainder
is charged to the actual square increment, not the worst-case increment
squared on every transition. No independence assumption is used.
-/
namespace Erdos773.FinitePowerTaylor
open Finset FiniteKernelCrossing
set_option maxHeartbeats 2500000

/-- Exact recurrence for the first-order remainder of a power. -/
lemma remainder_recurrence (x y : ℝ) (n : ℕ) :
    (x+y)^(n+3)-x^(n+3)-(n+3:ℕ)*x^(n+2)*y =
      (x+y)*((x+y)^(n+2)-x^(n+2)-(n+2:ℕ)*x^(n+1)*y)+
        (n+2:ℕ)*x^(n+1)*y^2 := by
  simp only [pow_succ,Nat.cast_add,Nat.cast_ofNat]
  ring

/-- A first-order power remainder, with its second-order factor explicit. -/
theorem remainder_bound (x y : ℝ) (n : ℕ) :
    |(x+y)^(n+2)-x^(n+2)-(n+2:ℕ)*x^(n+1)*y| ≤
      (n+2:ℕ)^2*(|x|+|y|)^n*y^2 := by
  induction n with
  | zero =>
    norm_num only [Nat.zero_add,Nat.cast_ofNat,pow_zero,pow_one,mul_one]
    have he : (x+y)^2-x^2-2*x*y = y^2 := by ring
    rw [he,abs_of_nonneg (sq_nonneg y)]
    nlinarith only [sq_nonneg y]
  | succ n ih =>
    change |(x+y)^(n+3)-x^(n+3)-(n+3:ℕ)*x^(n+2)*y| ≤
      (n+3:ℕ)^2*(|x|+|y|)^(n+1)*y^2
    rw [remainder_recurrence]
    have hterm1 : |(x+y)*((x+y)^(n+2)-x^(n+2)-(n+2:ℕ)*x^(n+1)*y)| ≤
        (n+2:ℕ)^2*(|x|+|y|)^(n+1)*y^2 := by
      rw [abs_mul]
      calc
        _ ≤ (|x|+|y|)*((n+2:ℕ)^2*(|x|+|y|)^n*y^2) :=
          mul_le_mul (abs_add_le x y) ih (abs_nonneg _) (by positivity)
        _ = _ := by rw [pow_succ]; ring
    have hterm2 : |(n+2:ℕ)*x^(n+1)*y^2| ≤
        (n+2:ℕ)*(|x|+|y|)^(n+1)*y^2 := by
      rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_pow,abs_of_nonneg (sq_nonneg y)]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg y)
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact pow_le_pow_left₀ (abs_nonneg x) (by linarith only [abs_nonneg y]) _
    have htri := (abs_add_le _ _).trans (add_le_add hterm1 hterm2)
    have hcoef : ((n+2:ℕ):ℝ)^2+(n+2:ℕ) ≤ (n+3:ℕ)^2 := by
      push_cast
      nlinarith only [Nat.cast_nonneg (α := ℝ) n]
    have hm := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ (|x|+|y|)^(n+1)*y^2 by positivity)
    nlinarith only [htri,hm]

/-- A convenient split coefficient for the Taylor remainder. -/
def coefficient (n : ℕ) : ℝ := (n+2:ℕ)^2*(2:ℝ)^n

lemma coefficient_nonneg (n : ℕ) : 0 ≤ coefficient n := by unfold coefficient; positivity

theorem split_remainder_bound (x y : ℝ) (n : ℕ) :
    |(x+y)^(n+2)-x^(n+2)-(n+2:ℕ)*x^(n+1)*y| ≤
      coefficient n*(|x|^n+|y|^n)*y^2 := by
  have hp : (|x|+|y|)^n ≤ (2:ℝ)^n*(|x|^n+|y|^n) := by
    apply (add_pow_le (abs_nonneg x) (abs_nonneg y) n).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.sub_le n 1)
  apply (remainder_bound x y n).trans
  have hm := mul_le_mul_of_nonneg_left hp (show (0:ℝ) ≤ (n+2:ℕ)^2 by positivity)
  have hm := mul_le_mul_of_nonneg_right hm (sq_nonneg y)
  unfold coefficient
  nlinarith only [hm]

/-- A bounded increment still pays its ACTUAL square, not the bound B^2. -/
theorem bounded_remainder (x y B : ℝ) (n : ℕ) (hy : |y| ≤ B) :
    |(x+y)^(n+2)-x^(n+2)-(n+2:ℕ)*x^(n+1)*y| ≤
      coefficient n*(|x|^n+B^n)*y^2 := by
  apply (split_remainder_bound x y n).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg y)
  apply mul_le_mul_of_nonneg_left _ (coefficient_nonneg n)
  exact add_le_add le_rfl (pow_le_pow_left₀ (abs_nonneg y) hy n)

/-- Finite-kernel natural-power drift. The mean and quadratic variation on
the right are exact conditional moments of the supplied observable. -/
theorem kernel_power_drift {σ : Type*} [Fintype σ] (K : Kernel σ) (s : σ)
    (X : σ → ℝ) (x B : ℝ) (n : ℕ)
    (hB : ∀ z, 0 < K.weight s z → |X z-x| ≤ B) :
    K.avg (fun z => (X z)^(n+2)-x^(n+2)) s ≤
      (n+2:ℕ)*x^(n+1)*K.avg (fun z => X z-x) s+
      coefficient n*(|x|^n+B^n)*K.avg (fun z => (X z-x)^2) s := by
  have hp (z : σ) (hz : 0 < K.weight s z) :
      (X z)^(n+2)-x^(n+2) ≤ (n+2:ℕ)*x^(n+1)*(X z-x)+
        coefficient n*(|x|^n+B^n)*(X z-x)^2 := by
    have hh := (abs_le.mp (bounded_remainder x (X z-x) B n (hB z hz))).2
    rw [add_sub_cancel] at hh
    linarith only [hh]
  have hh := K.avg_mono_support s hp
  rw [Kernel.avg_add,Kernel.avg_mul,Kernel.avg_mul] at hh
  exact hh

/-- Upper mean and variance estimates may be substituted after accounting
for the sign of the first-order coefficient. The signed drift is supplied
directly, so no positivity of the old observable is assumed. -/
theorem kernel_moment_bound {σ : Type*} [Fintype σ] (K : Kernel σ) (s : σ)
    (X : σ → ℝ) (x B D V : ℝ) (n : ℕ) (hB0 : 0 ≤ B)
    (hB : ∀ z, 0 < K.weight s z → |X z-x| ≤ B)
    (hD : x^(n+1)*K.avg (fun z => X z-x) s ≤ D)
    (hV : K.avg (fun z => (X z-x)^2) s ≤ V) :
    K.avg (fun z => (X z)^(n+2)-x^(n+2)) s ≤
      (n+2:ℕ)*D+coefficient n*(|x|^n+B^n)*V := by
  apply (kernel_power_drift K s X x B n hB).trans
  have hd := mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg (α := ℝ) (n+2))
  have hv := mul_le_mul_of_nonneg_left hV
    (show 0 ≤ coefficient n*(|x|^n+B^n) by exact mul_nonneg (coefficient_nonneg n) (by positivity))
  nlinarith only [hd,hv]

#print axioms remainder_recurrence
#print axioms remainder_bound
#print axioms split_remainder_bound
#print axioms bounded_remainder
#print axioms kernel_power_drift
#print axioms kernel_moment_bound
end Erdos773.FinitePowerTaylor
