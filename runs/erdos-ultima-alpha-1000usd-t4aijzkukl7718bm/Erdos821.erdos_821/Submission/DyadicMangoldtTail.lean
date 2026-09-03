import Submission.DyadicMangoldtMass

/-!
# A sharp weighted tail of dyadic harmonic Mangoldt masses

The leading term is the reciprocal-logarithm difference. The bounded
Mertens error contributes O(1/K^2), not O(1/K), across a long interval.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def dyadicMangoldtMass (k : ℕ) : ℝ :=
  harmonicMangoldtMass (2^(k+1))-harmonicMangoldtMass (2^k)

lemma dyadicMangoldtMass_eq_interval (k : ℕ) :
    dyadicMangoldtMass k = ∑ n ∈ Icc (2^k+1) (2^(k+1)), vonMangoldt n/(n : ℝ) := by
  exact (sum_natural_interval_sub _ _ _
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ k))).symm

lemma dyadicMangoldtMass_nonneg (k : ℕ) : 0 ≤ dyadicMangoldtMass k := by
  rw [dyadicMangoldtMass_eq_interval]
  exact sum_nonneg (fun _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))

lemma inv_sq_le_inv_difference (x : ℝ) (hx : 1 < x) :
    1/x^2 ≤ 1/(x-1)-1/x := by
  have hx0 : 0 < x := by linarith
  have hm : 0 < x-1 := by linarith
  have he : 1/(x-1)-1/x = 1/((x-1)*x) := by field_simp; ring
  rw [he]
  exact one_div_le_one_div_of_le (mul_pos hm hx0) (by nlinarith)

lemma sum_shifted_inv_sq_le (K R : ℕ) (hK : 2 ≤ K) :
    (∑ j ∈ range R, 1/((K : ℝ)+j)^2) ≤
      1/((K : ℝ)-1)-1/((K : ℝ)+R-1) := by
  let w : ℕ → ℝ := fun j => 1/((K : ℝ)+j-1)
  calc
    _ ≤ ∑ j ∈ range R, (w j-w (j+1)) := by
      apply sum_le_sum
      intro j hj
      have hx : 1 < (K : ℝ)+j := by
        have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
        linarith [Nat.cast_nonneg (α := ℝ) j]
      have hh := inv_sq_le_inv_difference ((K : ℝ)+j) hx
      convert hh using 1
      dsimp [w]
      push_cast
      congr 2
      ring
    _ = _ := by rw [sum_range_differences]; simp only [w,Nat.cast_zero,add_zero]

/-- The constant is absolute and the upper endpoint R is unrestricted. -/
theorem exists_dyadicMangoldtTail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ K R : ℕ, 2 ≤ K →
      (∑ j ∈ range R, dyadicMangoldtMass (K+j)/((K : ℝ)+j)^2) ≤
        Real.log 2*(1/((K : ℝ)-1)-1/((K : ℝ)+R-1))+2*C/(K : ℝ)^2 := by
  obtain ⟨C,hC,HC⟩ := exists_harmonicMangoldtMass_dyadic_bound
  refine ⟨C,hC,?_⟩
  intro K R hK
  let e : ℕ → ℝ := fun j => harmonicMangoldtMass (2^(K+j))-((K+j : ℕ) : ℝ)*Real.log 2
  let w : ℕ → ℝ := fun j => 1/((K : ℝ)+j)^2
  have hw : ∀ j, 0 ≤ w j := by intro j; dsimp [w]; positivity
  have hmono : ∀ j < R, w (j+1) ≤ w j := by
    intro j hj
    dsimp [w]
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    have hj0 : 0 ≤ (K : ℝ)+j := by positivity
    nlinarith only [hj0]
  have herr := weighted_difference_error_bound e w R C hC.le
    (fun j _ => HC (K+j)) (fun j _ => hw j) hmono
  have he : (∑ j ∈ range R, dyadicMangoldtMass (K+j)/((K : ℝ)+j)^2) =
      Real.log 2*(∑ j ∈ range R, w j)+∑ j ∈ range R, (e (j+1)-e j)*w j := by
    rw [mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    dsimp [dyadicMangoldtMass,e,w]
    rw [show K+(j+1)=K+j+1 by omega]
    push_cast
    ring
  rw [he]
  have herror : (∑ j ∈ range R, (e (j+1)-e j)*w j) ≤ 2*C/(K : ℝ)^2 := by
    apply (le_abs_self _).trans (herr.trans_eq ?_)
    simp only [w,Nat.cast_zero,add_zero]
    ring
  exact _root_.add_le_add
    (mul_le_mul_of_nonneg_left (sum_shifted_inv_sq_le K R hK) (Real.log_nonneg (by norm_num))) herror

end Erdos821.AnalyticSieve
