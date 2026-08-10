import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat BigOperators Filter Topology Algebra Polynomial

lemma eventually_constant_norm_test (p : ℚ[X]) (h_root : aeval xi_3 p ≠ 0) :
  ∃ V : ℤ, ∃ N : ℕ, ∀ n ≥ N, ‖(aeval (S n) p : Padic 3)‖ = (3 : ℝ) ^ V := by
  have h_cont : Continuous (fun x : Padic 3 => (aeval x p : Padic 3)) := by
    simp_rw [aeval_def]
    exact Polynomial.continuous_eval₂ p (algebraMap ℚ (Padic 3))
  have h_lim := h_cont.tendsto xi_3 |>.comp tendsto_S
  have h_pos : ‖aeval xi_3 p‖ > 0 := norm_pos_iff.mpr h_root
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_lim ‖aeval xi_3 p‖ h_pos
  use - (aeval xi_3 p).valuation, N
  intro n hn
  have h_dist := hN n hn
  rw [dist_eq_norm] at h_dist
  change ‖aeval (S n) p - aeval xi_3 p‖ < ‖aeval xi_3 p‖ at h_dist
  have h_eq : aeval (S n) p = aeval xi_3 p + (aeval (S n) p - aeval xi_3 p) := by ring
  have h_norm_eq : ‖aeval (S n) p‖ = ‖aeval xi_3 p‖ := by
    rw [h_eq, norm_add_eq_left_of_norm_lt h_dist]
  rw [h_norm_eq, Padic.norm_eq_zpow_neg_valuation h_root]
