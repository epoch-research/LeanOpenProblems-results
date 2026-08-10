import FormalConjectures.Util.ProblemImports

open Real BigOperators

set_option linter.style.namespace false
set_option linter.unusedVariables false
set_option linter.style.copyright.formalConjectures false

-- We want to prove: for any n and k, ∑_{i=1}^{k+1} 1 / (n + i) > log (n + k + 2) - log (n + 1)
lemma sum_inv_gt_log_sub (n : ℕ) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (1 / (n + 1 + i : ℝ))) > log (n + k + 2) - log (n + 1) := by
  induction k with
  | zero =>
    have h_sum : (∑ i ∈ Finset.range (0 + 1), (1 / (n + 1 + i : ℝ))) = 1 / (n + 1 : ℝ) := by
      simp
    rw [h_sum]
    push_cast
    have h_rhs : (n + (0 : ℝ) + 2) = n + 2 := by ring
    rw [h_rhs]
    have h1 : 0 < 1 + 1 / (n + 1 : ℝ) := by positivity
    have h2 : 1 + 1 / (n + 1 : ℝ) ≠ 1 := by
      intro h
      have h_ne : 1 / (n + 1 : ℝ) ≠ 0 := by positivity
      have : 1 / (n + 1 : ℝ) = 0 := by linarith
      exact h_ne this
    have h3 := Real.log_lt_sub_one_of_pos h1 h2
    have h4 : 1 + 1 / (n + 1 : ℝ) - 1 = 1 / (n + 1 : ℝ) := by ring
    rw [h4] at h3
    have h_div : 1 + 1 / (n + 1 : ℝ) = (n + 2) / (n + 1) := by
      have : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp; ring
    rw [h_div] at h3
    rw [log_div] at h3
    · linarith
    · positivity
    · positivity
  | succ k ih =>
    rw [Finset.sum_range_succ]
    push_cast
    -- LHS is sum + 1 / (n + 1 + k + 1)
    -- RHS is log (n + k + 3) - log (n + 1)
    -- We know: log (n + k + 3) - log (n + k + 2) < 1 / (n + k + 2)
    have h_log : log (1 + 1 / (n + k + 2 : ℝ)) < 1 / (n + k + 2 : ℝ) := by
      have h1 : 0 < 1 + 1 / (n + k + 2 : ℝ) := by positivity
      have h2 : 1 + 1 / (n + k + 2 : ℝ) ≠ 1 := by
        intro h
        have h_ne : 1 / (n + k + 2 : ℝ) ≠ 0 := by positivity
        have : 1 / (n + k + 2 : ℝ) = 0 := by linarith
        exact h_ne this
      have h3 := Real.log_lt_sub_one_of_pos h1 h2
      have h4 : 1 + 1 / (n + k + 2 : ℝ) - 1 = 1 / (n + k + 2 : ℝ) := by ring
      rwa [h4] at h3
    have h_log_rw : log (1 + 1 / (n + k + 2 : ℝ)) = log (n + k + 3) - log (n + k + 2) := by
      have h_div : 1 + 1 / (n + k + 2 : ℝ) = (n + k + 3) / (n + k + 2) := by
        have : (n + k + 2 : ℝ) ≠ 0 := by positivity
        field_simp; ring
      rw [h_div]
      rw [log_div]
      · positivity
      · positivity
    rw [h_log_rw] at h_log
    -- Now ih is: sum > log (n + k + 2) - log (n + 1)
    -- but ih contains casts of k + 1, so let's push_cast at ih too
    have ih' := ih
    push_cast at ih'
    -- Since n + 1 + k + 1 = n + k + 2 (by ring):
    have h_eq : (n + 1 + (k + 1 : ℝ)) = (n + k + 2 : ℝ) := by ring
    -- Since the goal has (n + 1 + (k + 1 : ℝ)), we can rewrite or linarith directly.
    -- Let's see if linarith can close it once we substitute the ring equality or just use it.
    -- We can rewrite the goal with these
    have h_goal_rhs : (n + (k + 1) + 2 : ℝ) = (n + k + 3 : ℝ) := by ring
    rw [h_eq, h_goal_rhs]
    linarith

lemma sum_inv_lt_log_sub (n : ℕ) (hn : 0 < n) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (1 / (n + 1 + i : ℝ))) < log (n + k + 1) - log n := by
  induction k with
  | zero =>
    have h_sum : (∑ i ∈ Finset.range (0 + 1), (1 / (n + 1 + i : ℝ))) = 1 / (n + 1 : ℝ) := by
      simp
    rw [h_sum]
    push_cast
    have h_rhs : (n + (0 : ℝ) + 1) = n + 1 := by ring
    rw [h_rhs]
    have h1 : 0 < 1 - 1 / (n + 1 : ℝ) := by
      have : (n : ℝ) > 0 := by positivity
      have : (n + 1 : ℝ) > 0 := by positivity
      have : 1 / (n + 1 : ℝ) < 1 := by
        rw [one_div_lt]
        · linarith
        · positivity
        · linarith
      linarith
    have h2 : 1 - 1 / (n + 1 : ℝ) ≠ 1 := by
      intro h
      have h_ne : 1 / (n + 1 : ℝ) ≠ 0 := by positivity
      have : 1 / (n + 1 : ℝ) = 0 := by linarith
      exact h_ne this
    have h3 := Real.log_lt_sub_one_of_pos h1 h2
    have h4 : 1 - 1 / (n + 1 : ℝ) - 1 = -1 / (n + 1 : ℝ) := by ring
    rw [h4] at h3
    have h_div : 1 - 1 / (n + 1 : ℝ) = n / (n + 1) := by
      have : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp; ring
    rw [h_div] at h3
    rw [log_div] at h3
    · linarith
    · positivity
    · positivity
  | succ k ih =>
    rw [Finset.sum_range_succ]
    generalize hS : (∑ i ∈ Finset.range (k + 1), (1 / (n + 1 + i : ℝ))) = S at ih ⊢
    push_cast
    have h_log : log (1 - 1 / (n + k + 2 : ℝ)) < -(1 / (n + k + 2 : ℝ)) := by
      have h1 : 0 < 1 - 1 / (n + k + 2 : ℝ) := by
        have : (n + k + 1 : ℝ) > 0 := by positivity
        have : (n + k + 2 : ℝ) > 0 := by positivity
        have : 1 / (n + k + 2 : ℝ) < 1 := by
          rw [one_div_lt]
          · linarith
          · positivity
          · linarith
        linarith
      have h2 : 1 - 1 / (n + k + 2 : ℝ) ≠ 1 := by
        intro h
        have h_ne : 1 / (n + k + 2 : ℝ) ≠ 0 := by positivity
        have : 1 / (n + k + 2 : ℝ) = 0 := by linarith
        exact h_ne this
      have h3 := Real.log_lt_sub_one_of_pos h1 h2
      have h4 : 1 - 1 / (n + k + 2 : ℝ) - 1 = -(1 / (n + k + 2 : ℝ)) := by ring
      rwa [h4] at h3
    have h_log_rw : log (1 - 1 / (n + k + 2 : ℝ)) = log (n + k + 1) - log (n + k + 2) := by
      have h_div : 1 - 1 / (n + k + 2 : ℝ) = (n + k + 1) / (n + k + 2) := by
        have : (n + k + 2 : ℝ) ≠ 0 := by positivity
        field_simp; ring
      rw [h_div]
      rw [log_div]
      · positivity
      · positivity
    rw [h_log_rw] at h_log
    have ih' := ih
    push_cast at ih'
    have h_eq : (n + 1 + (k + 1 : ℝ)) = (n + k + 2 : ℝ) := by ring
    have h_goal_rhs : (n + (k + 1) + 1 : ℝ) = (n + k + 2 : ℝ) := by ring
    rw [h_eq, h_goal_rhs]
    linarith


lemma harmonic_diff_eq_sum (a : ℕ) (k : ℕ) :
    (harmonic (a + k) : ℝ) - (harmonic a : ℝ) = ∑ i ∈ Finset.range k, (1 / (a + 1 + i : ℝ)) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    rw [Nat.add_succ, harmonic_succ]
    push_cast
    rw [inv_eq_one_div]
    have h_denom : (a + k + 1 : ℝ) = a + 1 + k := by ring
    rw [h_denom]
    linarith



