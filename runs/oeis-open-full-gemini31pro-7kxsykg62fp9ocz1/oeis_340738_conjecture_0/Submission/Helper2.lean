import Mathlib
import Submission.Helper

open Polynomial Real Nat MeasureTheory intervalIntegral Asymptotics Filter Topology Set

lemma hasDerivAt_poly_exp (P : ℝ[X]) (x : ℝ) :
  HasDerivAt (fun x => P.eval x * exp (1 - x)) (((derivative P).eval x - P.eval x) * exp (1 - x)) x := by
  have h1 : HasDerivAt (fun x => P.eval x) ((derivative P).eval x) x := P.hasDerivAt x
  have h2 : HasDerivAt (fun x => exp (1 - x)) (- exp (1 - x)) x := by
    have hd1 : HasDerivAt (fun x : ℝ => 1) (0:ℝ) x := hasDerivAt_const x (1:ℝ)
    have hd2 : HasDerivAt (fun x : ℝ => x) (1:ℝ) x := hasDerivAt_id x
    have hd3 : HasDerivAt (fun x : ℝ => 1 - x) (0 - 1 : ℝ) x := HasDerivAt.sub hd1 hd2
    have hd4 := HasDerivAt.exp hd3
    simpa using hd4
  have h3 := HasDerivAt.mul h1 h2
  convert h3 using 1; ring

lemma integral_poly_exp (P : ℝ[X]) :
  ∫ x in (0:ℝ)..1, ((P - derivative P).eval x) * exp (1 - x) = P.eval 0 * exp 1 - P.eval 1 := by
  have h_deriv : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt (fun x => - (P.eval x * exp (1 - x))) (((P - derivative P).eval x) * exp (1 - x)) x := by
    intro x _
    have h1 := hasDerivAt_poly_exp P x
    have h2 := HasDerivAt.neg h1
    convert h2 using 1; simp; ring
  have h_cont : Continuous (fun x : ℝ => ((P - derivative P).eval x) * exp (1 - x)) := by
    apply Continuous.mul
    · exact (P - derivative P).continuous
    · exact continuous_exp.comp (continuous_const.sub continuous_id)
  have h_int := integral_eq_sub_of_hasDerivAt h_deriv (h_cont.intervalIntegrable _ _)
  rw [h_int]; simp; ring

noncomputable def I_k (k : ℕ) : ℝ := ∫ x in (0:ℝ)..1, (P_poly k).eval x * exp (1 - x)

lemma P_poly_cont (k : ℕ) : Continuous (fun x => (P_poly k).eval x * exp (1 - x)) := by
  apply Continuous.mul
  · exact (P_poly k).continuous
  · exact continuous_exp.comp (continuous_const.sub continuous_id)

lemma I_k_recurrence_helper (k : ℕ) (hk : 1 ≤ k) :
  I_k (k + 1) + (4 * (k : ℝ) + 2) * I_k k - I_k (k - 1) =
  ∫ x in (0:ℝ)..1, (P_poly (k + 1) + C (4 * (k : ℝ) + 2) * P_poly k - P_poly (k - 1)).eval x * exp (1 - x) := by
  dsimp [I_k]
  have h_mul : (4 * (k : ℝ) + 2) * ∫ x in (0:ℝ)..1, (P_poly k).eval x * exp (1 - x) = ∫ x in (0:ℝ)..1, (4 * (k : ℝ) + 2) * ((P_poly k).eval x * exp (1 - x)) := by
    exact (intervalIntegral.integral_smul (4 * (k : ℝ) + 2) (fun x => (P_poly k).eval x * exp (1 - x))).symm
  rw [h_mul, ← intervalIntegral.integral_add, ← intervalIntegral.integral_sub]
  · congr 1; ext x; simp; ring
  · apply Continuous.intervalIntegrable; apply Continuous.add
    · exact P_poly_cont (k + 1)
    · apply Continuous.mul continuous_const (P_poly_cont k)
  · exact Continuous.intervalIntegrable (P_poly_cont (k - 1)) _ _
  · exact Continuous.intervalIntegrable (P_poly_cont (k + 1)) _ _
  · apply Continuous.intervalIntegrable; apply Continuous.mul continuous_const (P_poly_cont k)

lemma g_poly_eval_zero (k : ℕ) (hk : 1 ≤ k) : (g_poly k).eval 0 = 0 := by
  dsimp [g_poly]; simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_add, eval_C, eval_one]
  have : (0 * (1 - 0) : ℝ) ^ k = 0 := by rw [sub_zero, zero_mul, zero_pow]; omega
  rw [this]; ring

lemma g_poly_eval_one (k : ℕ) (hk : 1 ≤ k) : (g_poly k).eval 1 = 0 := by
  dsimp [g_poly]; simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_add, eval_C, eval_one]
  have : (1 * (1 - 1) : ℝ) ^ k = 0 := by rw [sub_self, mul_zero, zero_pow]; omega
  rw [this]; ring

lemma I_k_recurrence (k : ℕ) (hk : 1 ≤ k) :
  I_k (k + 1) + (4 * (k : ℝ) + 2) * I_k k - I_k (k - 1) = 0 := by
  rw [I_k_recurrence_helper k hk]
  have H_eq : P_poly (k + 1) + C (4 * (k : ℝ) + 2) * P_poly k - P_poly (k - 1) = derivative (g_poly k) - g_poly k := by
    have h1 := P_poly_identity k hk
    calc
      P_poly (k + 1) + C (4 * (k : ℝ) + 2) * P_poly k - P_poly (k - 1) = P_poly (k + 1) + C (4 * (k : ℝ) + 2) * P_poly k - P_poly (k - 1) + g_poly k - g_poly k := by ring
      _ = derivative (g_poly k) - g_poly k := by rw [← h1]
  rw [H_eq]
  have H_int := integral_poly_exp (- g_poly k)
  have H_eval : (- g_poly k - derivative (- g_poly k)) = derivative (g_poly k) - g_poly k := by simp; ring
  have H_eval2 : (fun x => (derivative (g_poly k) - g_poly k).eval x * exp (1 - x)) = (fun x => ((- g_poly k - derivative (- g_poly k)).eval x) * exp (1 - x)) := by ext x; congr 1; rw [H_eval]
  rw [H_eval2, H_int]
  have hz := g_poly_eval_zero k hk
  have ho := g_poly_eval_one k hk
  simp only [eval_neg]; rw [hz, ho]; ring
