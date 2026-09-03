import Submission.LogarithmicCovariance

/-! Elementary L1 perturbation bounds for finite centered covariance. -/
namespace Erdos972CovariancePerturbation

open Finset
open Erdos972LogarithmicCovariance

lemma covariance_comm (N : ℕ) (f g : ℕ → ℝ) : covariance N f g = covariance N g f := by
  unfold covariance
  have he : total N (fun n => f n*g n) = total N (fun n => g n*f n) := by
    apply sum_congr rfl
    intro n hn
    ring
  rw [he]
  ring

lemma covariance_sub_right (N : ℕ) (f g h : ℕ → ℝ) :
    covariance N f (fun n => g n-h n) = covariance N f g-covariance N f h := by
  simp only [covariance, total, mul_sub, sum_sub_distrib]
  ring

lemma covariance_bound_l1 {N : ℕ} (hN : 0 < N) (f g : ℕ → ℝ) {A : ℝ}
    (hf : ∀ n ∈ Ioc 0 N, |f n| ≤ A) :
    |covariance N f g| ≤ 2*A*total N (fun n => |g n|) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hA0 : 0 ≤ A := (abs_nonneg (f 1)).trans (hf 1 (mem_Ioc.mpr ⟨by omega, hN⟩))
  have hg0 : 0 ≤ total N (fun n => |g n|) := sum_nonneg (fun n hn => abs_nonneg _)
  have hp : |total N (fun n => f n*g n)| ≤ A*total N (fun n => |g n|) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ n ∈ Ioc 0 N, A*|g n| := by
        apply sum_le_sum
        intro n hn
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hf n hn) (abs_nonneg _)
      _ = _ := by rw [total, mul_sum]
  have hfg : |total N f*total N g/N| ≤ A*total N (fun n => |g n|) := by
    rw [abs_div, abs_mul, abs_of_nonneg hN0.le]
    apply (div_le_iff₀ hN0).mpr
    have hh := mul_le_mul (total_abs_le hf) (abs_sum_le_sum_abs (fun n => g n) (Ioc 0 N))
      (abs_nonneg _) (mul_nonneg hN0.le hA0)
    exact hh.trans_eq (by unfold total; ring)
  unfold covariance
  exact (abs_sub _ _).trans (by linarith only [hp, hfg])

lemma covariance_second_perturb {N : ℕ} (hN : 0 < N) (f g G : ℕ → ℝ) {A : ℝ}
    (hf : ∀ n ∈ Ioc 0 N, |f n| ≤ A) :
    |covariance N f g-covariance N f G| ≤ 2*A*total N (fun n => |g n-G n|) := by
  rw [← covariance_sub_right]
  exact covariance_bound_l1 hN f (fun n => g n-G n) hf

lemma covariance_l1_perturb {N : ℕ} (hN : 0 < N) (f g F G : ℕ → ℝ) {A B : ℝ}
    (hF : ∀ n ∈ Ioc 0 N, |F n| ≤ A) (hg : ∀ n ∈ Ioc 0 N, |g n| ≤ B) :
    |covariance N f g-covariance N F G| ≤
      2*B*total N (fun n => |f n-F n|)+2*A*total N (fun n => |g n-G n|) := by
  have hh := covariance_second_perturb hN g f F hg
  rw [covariance_comm N g f, covariance_comm N g F] at hh
  have hk := covariance_second_perturb hN F g G hF
  exact (abs_sub_le _ (covariance N F g) _).trans (add_le_add hh hk)

#print axioms covariance_l1_perturb

end Erdos972CovariancePerturbation
