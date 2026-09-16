import Submission.Lemmas
import Submission.Lemmas2
import Submission.Spec
import Mathlib

open Nat Finset

lemma sumD_eq_zero_iff (M : ℕ) : sumD M = 0 ↔ M = 0 := by
  induction' M using Nat.strong_induction_on with M ih
  constructor
  · intro h
    by_contra h_neq
    have H : sumD M = M % 10 + sumD (M / 10) := sumD_pos M h_neq
    rw [h] at H
    have H1 : M % 10 = 0 := by omega
    have H2 : sumD (M / 10) = 0 := by omega
    have h_div_lt : M / 10 < M := Nat.div_lt_self (Nat.pos_of_ne_zero h_neq) (by decide)
    have : M / 10 = 0 := (ih (M / 10) h_div_lt).mp H2
    have e : M = 10 * (M / 10) + M % 10 := (Nat.div_add_mod M 10).symm
    rw [this, H1] at e
    omega
  · intro h
    subst h
    exact sumD_zero

lemma extract_y (n : ℕ) (x : ℕ) (hx : x ∈ reachable_zeroless_factorials (n + 1)) :
  ∃ y ∈ reachable_zeroless_factorials n, x = (n + 1) * y ∨ x = remove_zeros ((n + 1) * y) := by
  unfold reachable_zeroless_factorials at hx
  have h1 : ∃ a ∈ reachable_zeroless_factorials n, x ∈ {(n + 1) * a, remove_zeros ((n + 1) * a)} := Finset.mem_biUnion.mp hx
  rcases h1 with ⟨y, hy, h_insert⟩
  use y
  constructor
  · exact hy
  · simp at h_insert
    exact h_insert

lemma reachable_ge_one_strong (n : ℕ) (x : ℕ) (hx : x ∈ reachable_zeroless_factorials n) : x ≥ 1 := by
  induction' n with n ih generalizing x
  · unfold reachable_zeroless_factorials at hx
    simp at hx
    omega
  · rcases extract_y n x hx with ⟨y, hy, h_eq⟩
    have hy1 : y ≥ 1 := ih y hy
    cases h_eq with
    | inl h =>
      subst h
      have h1 : n + 1 > 0 := by omega
      have h2 : y > 0 := by omega
      have := Nat.mul_pos h1 h2
      omega
    | inr h =>
      subst h
      have h1 : n + 1 > 0 := by omega
      have h2 : y > 0 := by omega
      have M_pos : (n + 1) * y > 0 := Nat.mul_pos h1 h2
      have h_sumD : sumD ((n + 1) * y) ≠ 0 := by
        intro h0
        have := sumD_eq_zero_iff ((n + 1) * y)
        have H := this.mp h0
        omega
      have h_sumD_rz : sumD (remove_zeros ((n + 1) * y)) ≠ 0 := by
        rw [sumD_remove_zeros]
        exact h_sumD
      by_contra h_contra
      have : remove_zeros ((n + 1) * y) = 0 := by omega
      rw [this] at h_sumD_rz
      rw [sumD_zero] at h_sumD_rz
      exact h_sumD_rz rfl
