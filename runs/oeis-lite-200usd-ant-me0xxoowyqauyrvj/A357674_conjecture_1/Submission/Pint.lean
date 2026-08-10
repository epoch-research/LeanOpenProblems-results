import Mathlib

open Nat Finset BigOperators

/-- nonneg version of the ultrametric inequality for finite sums. -/
theorem sum_nonneg_val (p : ℕ) [hp : Fact p.Prime] {n : ℕ} {F : ℕ → ℚ}
    (hF : ∀ i, i < n → 0 ≤ padicValRat p (F i)) :
    0 ≤ padicValRat p (∑ i ∈ Finset.range n, F i) := by
  induction n with
  | zero => simp
  | succ d hd =>
    rw [Finset.sum_range_succ]
    by_cases h : (∑ x ∈ Finset.range d, F x) + F d = 0
    · rw [h]; simp
    · refine le_trans ?_ (padicValRat.min_le_padicValRat_add h)
      refine le_min (hd (fun i hi => hF _ (lt_trans hi (lt_add_one _)))) (hF d (lt_add_one _))

/-- p-integrality of Bernoulli numbers for indices below `p-1`,
proved elementarily from the Bernoulli recurrence. -/
theorem bernoulli_padic_nonneg (p : ℕ) [hp : Fact p.Prime] :
    ∀ n : ℕ, n + 1 < p → 0 ≤ padicValRat p (bernoulli n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0; simp [bernoulli_zero]
    · -- n ≥ 1, so n+1 ≥ 2
      have hrec := sum_bernoulli (n+1)
      rw [if_neg (by omega : n + 1 ≠ 1)] at hrec
      rw [Finset.sum_range_succ] at hrec
      -- C(n+1,n) = n+1
      have hcc : ((n+1).choose n : ℚ) = (n+1 : ℚ) := by
        have h1 : (n+1).choose n = n + 1 := by
          have h2 := Nat.choose_symm (Nat.le_succ n)
          have h3 : (n+1) - n = 1 := by omega
          rw [h3] at h2
          rw [← h2, Nat.choose_one_right]
        rw [h1]; push_cast; ring
      rw [hcc] at hrec
      -- so (n+1)*B n = - S, where S = ∑_{k<n} C(n+1,k) B k
      set S := ∑ x ∈ Finset.range n, ((n+1).choose x : ℚ) * bernoulli x with hS
      have hp1 : ((n+1 : ℚ)) ≠ 0 := by positivity
      have key : bernoulli n = (- S) / (n+1) := by
        field_simp
        linarith [hrec]
      have hval_den : padicValRat p ((n+1 : ℚ)) = 0 := by
        have hnd : ¬ (p ∣ (n+1)) := by
          intro hdvd
          have := Nat.le_of_dvd (by omega) hdvd
          omega
        rw [show ((n+1 : ℚ)) = ((n+1 : ℕ) : ℚ) by push_cast; ring, padicValRat.of_nat]
        rw [padicValNat.eq_zero_of_not_dvd hnd]; rfl
      have hSval : 0 ≤ padicValRat p S := by
        apply sum_nonneg_val
        intro i hi
        by_cases hbi : bernoulli i = 0
        · simp [hbi]
        · rw [padicValRat.mul
            (by exact_mod_cast (Nat.choose_pos (by omega : i ≤ n+1)).ne') hbi]
          have hc : 0 ≤ padicValRat p (((n+1).choose i : ℚ)) :=
            zero_le_padicValRat_of_nat _
          have hb : 0 ≤ padicValRat p (bernoulli i) := ih i hi (by omega)
          linarith
      rw [key]
      by_cases hS0 : S = 0
      · rw [hS0]; simp
      · rw [padicValRat.div (neg_ne_zero.mpr hS0) hp1, padicValRat.neg, hval_den, sub_zero]
        exact hSval
