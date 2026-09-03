import Submission.SubexponentialEulerCost

/-!
# Finite Rankin bounds with explicit divisor-order dependence

These upper estimates do not assert a lower bound on shifted primes.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta Topology

namespace Erdos821.HigherDivisors

set_option maxHeartbeats 2000000

lemma tau_cast (k n : ℕ) : (tau k n : ℝ) = ((ζ : ArithmeticFunction ℝ)^k) n := by
  have h : (((ζ : ArithmeticFunction ℕ)^k : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) =
      (ζ : ArithmeticFunction ℝ)^k := by
    induction k with
    | zero => simp
    | succ k ih => rw [_root_.pow_succ, natCoe_mul, ih, _root_.pow_succ]
  exact congrArg (fun f : ArithmeticFunction ℝ => f n) h

lemma tau_real_nonneg (k n : ℕ) : 0 ≤ ((ζ : ArithmeticFunction ℝ)^k) n := by
  rw [← tau_cast]
  positivity

/-- A finite Dirichlet series of the k-fold convolution is bounded by the
k-th power of the finite base series. -/
lemma partial_dirichlet_moment_le (k A : ℕ) (s : ℝ) :
    (∑ n ∈ Finset.Icc 1 A, (tau k n : ℝ) * (n : ℝ)^(-s)) ≤
      (∑ n ∈ Finset.Icc 1 A, (n : ℝ)^(-s))^k := by
  simp_rw [tau_cast]
  induction k with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply, ite_mul, one_mul, zero_mul]
    by_cases hA : 1 ≤ A <;> simp [hA]
  | succ k ih =>
    rw [_root_.pow_succ', AnalyticSieve.sum_convolution_weighted _ _ _ (le_refl A)]
    calc
      _ ≤ ∑ m ∈ Finset.Icc 1 A, ∑ n ∈ Finset.Icc 1 A,
          (m : ℝ)^(-s) * (((ζ : ArithmeticFunction ℝ)^k) n * (n : ℝ)^(-s)) := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro n hn
        by_cases hmn : m*n ≤ A
        · simp only [hmn, if_true, natCoe_apply,
            zeta_apply_ne (by have := (Finset.mem_Icc.mp hm).1; omega : m ≠ 0),
            Nat.cast_one, one_mul, Nat.cast_mul,
            Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
          exact le_of_eq (by ring)
        · simp only [hmn, if_false]
          exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
            (mul_nonneg (tau_real_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      _ = (∑ m ∈ Finset.Icc 1 A, (m : ℝ)^(-s)) *
          (∑ n ∈ Finset.Icc 1 A, ((ζ : ArithmeticFunction ℝ)^k) n * (n : ℝ)^(-s)) := by
        simp_rw [← Finset.mul_sum]
        rw [Finset.sum_mul]
      _ ≤ _ := by
        rw [_root_.pow_succ']
        exact mul_le_mul_of_nonneg_left ih (Finset.sum_nonneg (fun n _ => by positivity))

lemma partial_pseries_le (A : ℕ) (s : ℝ) (hs : 0 < s) :
    (∑ n ∈ Finset.Icc 1 A, (n : ℝ)^(-(1+s))) ≤ 1+s⁻¹ := by
  by_cases hA : A = 0
  · subst A
    simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), Finset.sum_empty]
    positivity
  have hA1 : 1 ≤ A := by omega
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA1
  have hf : AntitoneOn (fun x : ℝ => x^(-(1+s))) (Set.Icc 1 (A : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hi := AntitoneOn.sum_le_integral_Ico hA1
    (show AntitoneOn (fun x : ℝ => x^(-(1+s))) (Set.Icc ((1 : ℕ) : ℝ) (A : ℝ)) by
      simpa only [Nat.cast_one] using hf)
  have he : (∑ n ∈ Finset.Icc 1 A, (n : ℝ)^(-(1+s))) =
      1 + ∑ n ∈ Finset.Ico 1 A, ((n+1 : ℕ) : ℝ)^(-(1+s)) := by
    rw [Finset.sum_Ico_add' (fun n : ℕ => (n : ℝ)^(-(1+s))) 1 A 1]
    have hset : Finset.Icc 1 A = insert 1 (Finset.Ico (1+1) (A+1)) := by
      ext n
      simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    norm_num
  rw [he]
  simp only [Nat.cast_one] at hi
  apply _root_.add_le_add le_rfl (hi.trans ?_)
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [Set.uIcc_of_le hAR]
    simp⟩)]
  have he : -(1+s)+1 = -s := by ring
  rw [he, Real.one_rpow, div_neg, ← neg_div, neg_sub]
  apply (div_le_iff₀ hs).mpr
  rw [inv_mul_cancel₀ hs.ne']
  have hpow : 0 ≤ (A : ℝ)^(-s) := Real.rpow_nonneg (Nat.cast_nonneg A) _
  linarith

/-- Finite Rankin's trick; the cutoff exponent is a free positive parameter. -/
theorem harmonicMoment_rankin (k A : ℕ) (s : ℝ) (hs : 0 < s) :
    harmonicMoment k A ≤ (A : ℝ)^s * (1+s⁻¹)^k := by
  calc
    _ ≤ (A : ℝ)^s * (∑ n ∈ Finset.Icc 1 A, (tau k n : ℝ) * (n : ℝ)^(-(1+s))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnA : (n : ℝ) ≤ A := by exact_mod_cast (Finset.mem_Icc.mp hn).2
      calc
        (tau k n : ℝ)/(n : ℝ) = (n : ℝ)^s *
            ((tau k n : ℝ)*(n : ℝ)^(-(1+s))) := by
          rw [mul_left_comm, ← Real.rpow_add hnR,
            (show s + -(1+s) = -1 by ring), Real.rpow_neg_one]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hnR.le hnA hs.le) (by positivity)
    _ ≤ (A : ℝ)^s * (∑ n ∈ Finset.Icc 1 A, (n : ℝ)^(-(1+s)))^k :=
      mul_le_mul_of_nonneg_left (partial_dirichlet_moment_le k A (1+s)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun n _ => by positivity))
        (partial_pseries_le A s hs) k) (by positivity)

/-- Choosing s=k/log(A) preserves the (e/k)^k scale. -/
theorem harmonicMoment_rankin_optimized (k A : ℕ) (hk : 0 < k) (hA : 1 < A) :
    harmonicMoment k A ≤ (Real.exp 1 / (k : ℝ))^k * (Real.log A + k)^k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hAR : (1 : ℝ) < A := by exact_mod_cast hA
  have hL : 0 < Real.log A := Real.log_pos hAR
  have h := harmonicMoment_rankin k A ((k : ℝ)/Real.log A) (div_pos hkR hL)
  apply h.trans_eq
  have he : (A : ℝ)^((k : ℝ)/Real.log A) = Real.exp (k : ℝ) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    congr 1
    field_simp
  rw [he]
  rw [show Real.exp (k : ℝ) = (Real.exp 1)^k by simpa only [mul_one] using Real.exp_nat_mul 1 k]
  rw [← mul_pow, ← mul_pow]
  congr 1
  field_simp
  ring

end Erdos821.HigherDivisors
