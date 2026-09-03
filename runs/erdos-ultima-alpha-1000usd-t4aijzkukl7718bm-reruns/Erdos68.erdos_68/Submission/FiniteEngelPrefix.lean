import Submission.ModifiedEngel

/-!
# Rational inputs with every finite factorial prefix

This file does not prove or disprove Erdős 68. It proves that every finite
prefix of the target's strict Engel multipliers also occurs for a rational
input. The chosen rational input deviates at the immediately following step.
-/

namespace Erdos68Development

lemma remainder_strictAnti : StrictAnti remainder := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [remainder_succ]
  linarith [term_pos n]

lemma strictEngelRatio_of_interval {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    (hl : term n < r) (hu : r ≤ remainder n) :
    strictEngelRatio (n + 1).factorial r = (n + 2 : ℤ) := by
  have hr : 0 < r := (term_pos n).trans hl
  have ha : (0 : ℝ) < (n + 1).factorial := by positivity
  have harg : (1 / remainder n + 1) / (n + 1).factorial ≤
      (1 / r + 1) / (n + 1).factorial := by
    apply div_le_div_of_nonneg_right _ ha.le
    linarith [one_div_le_one_div_of_le hr hu]
  have hlo := (strictEngel_argument_bounds hn).1.trans_le harg
  have hinv : 1 / r < (n + 2).factorial - 1 := by
    have hh := one_div_lt_one_div_of_lt (term_pos n) hl
    simpa only [term, one_div_one_div] using hh
  have hhi : (1 / r + 1) / (n + 1).factorial < (n + 2 : ℝ) := by
    apply (div_lt_iff₀ ha).mpr
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ] at hinv
    push_cast at hinv
    nlinarith
  have hf : ⌊(1 / r + 1) / (n + 1).factorial⌋ = (n + 1 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hlo.le
    · push_cast
      linarith
  simp only [strictEngelRatio, hf]
  ring

lemma strictEngelStep_finite_remainder {M n : ℕ}
    (hn : 1 ≤ n) (hM : n + 1 < M) :
    strictEngelStep ((n + 1).factorial, remainder n - remainder M) =
      (((n + 2).factorial : ℝ), remainder (n + 1) - remainder M) := by
  have hl : term n < remainder n - remainder M := by
    have hh := remainder_strictAnti hM
    rw [remainder_succ] at hh
    linarith
  have hu : remainder n - remainder M ≤ remainder n := by
    linarith [remainder_pos M]
  unfold strictEngelStep
  rw [strictEngelRatio_of_interval hn hl hu]
  have hf : (n + 2 : ℝ) * (n + 1).factorial = (n + 2).factorial := by
    exact_mod_cast (Nat.factorial_succ (n + 1)).symm
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat, hf]
  rw [remainder_succ]
  dsimp [term]
  congr 1
  ring

/-- The input is a rational finite partial sum, with the initial term removed. -/
def finiteEngelInput (M : ℕ) : ℚ :=
  (∑ k ∈ Finset.range M, 1 / ((k + 2).factorial - 1 : ℚ)) - 1

lemma cast_finiteEngelInput (M : ℕ) :
    (finiteEngelInput M : ℝ) = remainder 1 - remainder M := by
  simp only [finiteEngelInput, Rat.cast_sub, Rat.cast_sum, Rat.cast_div,
    Rat.cast_one, Rat.cast_natCast, remainder, Finset.sum_range_one, term]
  ring

lemma strictEngel_iterate_finite {M n : ℕ} (h : n + 2 ≤ M) :
    (strictEngelStep^[n]) (2, (finiteEngelInput M : ℝ)) =
      (((n + 2).factorial : ℝ), remainder (n + 1) - remainder M) := by
  induction n with
  | zero => simp [cast_finiteEngelInput]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      strictEngelStep_finite_remainder (n := n + 1) (M := M) (by omega) (by omega)

lemma strictEngelRatio_single_term (n : ℕ) :
    strictEngelRatio (n + 1).factorial (term n) = (n + 3 : ℤ) := by
  have hf : (n + 2 : ℝ) * (n + 1).factorial = (n + 2).factorial := by
    exact_mod_cast (Nat.factorial_succ (n + 1)).symm
  have ha : (0 : ℝ) < (n + 1).factorial := by positivity
  have harg : (1 / term n + 1) / (n + 1).factorial = (n + 2 : ℝ) := by
    simp only [term, one_div_one_div, sub_add_cancel]
    rw [← hf, mul_div_cancel_right₀ _ ha.ne']
  simp only [strictEngelRatio, harg]
  rw [show (n + 2 : ℝ) = ((n + 2 : ℤ) : ℝ) by push_cast; rfl,
    Int.floor_intCast]
  ring

/-- Every finite multiplier prefix occurs at a positive rational input.
The very next multiplier is one larger than the target's multiplier. -/
theorem rational_inputs_with_arbitrary_finite_prefix (N : ℕ) :
    ∃ r : ℚ, 0 < r ∧
      (∀ n ≤ N, ((strictEngelStep^[n]) (2, (r : ℝ))).1 =
        ((n + 2).factorial : ℝ)) ∧
      strictEngelRatio ((strictEngelStep^[N]) (2, (r : ℝ))).1
        ((strictEngelStep^[N]) (2, (r : ℝ))).2 = (N + 4 : ℤ) := by
  refine ⟨finiteEngelInput (N + 2), ?_, ?_, ?_⟩
  · have hp := remainder_strictAnti (show 1 < N + 2 by omega)
    have hr : (0 : ℝ) < (finiteEngelInput (N + 2) : ℝ) := by
      rw [cast_finiteEngelInput]
      linarith
    exact_mod_cast hr
  · intro n hn
    rw [strictEngel_iterate_finite (by omega : n + 2 ≤ N + 2)]
  · rw [strictEngel_iterate_finite (le_refl (N + 2))]
    have he : remainder (N + 1) - remainder (N + 2) = term (N + 1) := by
      have hs : remainder (N + 2) = remainder (N + 1) - term (N + 1) := by
        simpa only [Nat.add_assoc, Nat.reduceAdd] using remainder_succ (N + 1)
      rw [hs]
      ring
    simp only [he]
    simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_one,
      Int.reduceAdd] using strictEngelRatio_single_term (N + 1)

#print axioms rational_inputs_with_arbitrary_finite_prefix

end Erdos68Development
