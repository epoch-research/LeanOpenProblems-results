import Submission.CorrectedApprox

/-!
# Exact modified Engel steps

This auxiliary file verifies that the strict modified Engel rule recovers the
factorial multipliers. It does not assert rational termination of that rule,
and is not a proof of the irrationality conjecture.
-/

namespace Erdos68Development

noncomputable def remainder (n : ℕ) : ℝ :=
  (∑' k : ℕ, term k) - ∑ k ∈ Finset.range n, term k

noncomputable def strictEngelRatio (A r : ℝ) : ℤ :=
  ⌊(1 / r + 1) / A⌋ + 1

lemma remainder_pos (n : ℕ) : 0 < remainder n :=
  (partial_sum_error n).1

lemma remainder_succ (n : ℕ) :
    remainder (n + 1) = remainder n - term n := by
  simp only [remainder, Finset.sum_range_succ]
  ring

lemma remainder_gt_term (n : ℕ) : term n < remainder n := by
  have h := remainder_pos (n + 1)
  rw [remainder_succ] at h
  linarith

lemma strictEngel_bound_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < (n + 1 : ℝ) * (n + 1).factorial - 1 := by
  have hf : (2 : ℝ) ≤ (n + 1).factorial := by
    have h := Nat.factorial_le (show 2 ≤ n + 1 by omega)
    norm_num at h
    exact_mod_cast h
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

lemma remainder_lt_strictEngel_bound {n : ℕ} (hn : 1 ≤ n) :
    remainder n < 1 / ((n + 1 : ℝ) * (n + 1).factorial - 1) := by
  rcases eq_or_lt_of_le hn with h | h
  · subst n
    have hu := sum_bounds.2
    have ht : term 0 = 1 := by norm_num [term]
    simp only [remainder, Finset.sum_range_one, ht]
    norm_num
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hu := sum_lt_correctedApprox k
    rw [cast_correctedApprox] at hu
    have hr : remainder (k + 2) <
        1 / ((k + 3 : ℝ) * (k + 3).factorial) := by
      unfold remainder
      linarith
    have he : k + 2 + 1 = k + 3 := by omega
    have he' : (k : ℝ) + 2 + 1 = k + 3 := by ring
    have hb : 0 < (k + 3 : ℝ) * (k + 3).factorial - 1 := by
      simpa only [he, Nat.cast_add, Nat.cast_ofNat, he'] using
        strictEngel_bound_pos (show 1 ≤ k + 2 by omega)
    have hg := hr.trans (one_div_lt_one_div_of_lt hb (show
      (k + 3 : ℝ) * (k + 3).factorial - 1 <
        (k + 3 : ℝ) * (k + 3).factorial by linarith))
    simpa only [he, Nat.cast_add, Nat.cast_ofNat, he'] using hg

lemma strictEngel_argument_bounds {n : ℕ} (hn : 1 ≤ n) :
    (n + 1 : ℝ) < (1 / remainder n + 1) / (n + 1).factorial ∧
      (1 / remainder n + 1) / (n + 1).factorial < (n + 2 : ℝ) := by
  have hr := remainder_pos n
  have ha : (0 : ℝ) < (n + 1).factorial := by positivity
  have hb := strictEngel_bound_pos hn
  have hl := remainder_gt_term n
  have hu := remainder_lt_strictEngel_bound hn
  have hd := denom_pos n
  have hinv_lower : (n + 1 : ℝ) * (n + 1).factorial - 1 <
      1 / remainder n := by
    have hh := one_div_lt_one_div_of_lt hr hu
    simpa only [one_div_one_div] using hh
  have hinv_upper : 1 / remainder n < (n + 2).factorial - 1 := by
    have hh := one_div_lt_one_div_of_lt (term_pos n) hl
    simpa only [term, one_div_one_div] using hh
  constructor
  · apply (lt_div_iff₀ ha).mpr
    linarith
  · apply (div_lt_iff₀ ha).mpr
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ] at hinv_upper
    push_cast at hinv_upper
    nlinarith

lemma strictEngelRatio_remainder {n : ℕ} (hn : 1 ≤ n) :
    strictEngelRatio (n + 1).factorial (remainder n) = (n + 2 : ℤ) := by
  obtain ⟨hl, hu⟩ := strictEngel_argument_bounds hn
  have hf : ⌊(1 / remainder n + 1) / (n + 1).factorial⌋ = (n + 1 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hl.le
    · push_cast
      linarith
  simp only [strictEngelRatio, hf]
  ring

/-- The strict choice always leaves a positive remainder, for every positive
input, not only for the target series. Thus nontermination alone cannot be an
irrationality criterion for this particular rule. -/
lemma strictEngel_step_pos {A r : ℝ} (hA : 0 < A) (hr : 0 < r) :
    0 < (strictEngelRatio A r : ℝ) * A - 1 ∧
      0 < r - 1 / ((strictEngelRatio A r : ℝ) * A - 1) := by
  have hf : (1 / r + 1) / A < (strictEngelRatio A r : ℝ) := by
    simpa only [strictEngelRatio, Int.cast_add, Int.cast_one] using
      Int.lt_floor_add_one ((1 / r + 1) / A)
  have hh := (div_lt_iff₀ hA).mp hf
  have hi : 0 < 1 / r := one_div_pos.mpr hr
  have hd : 1 / r < (strictEngelRatio A r : ℝ) * A - 1 := by linarith
  refine ⟨hi.trans hd, ?_⟩
  have h := one_div_lt_one_div_of_lt hi hd
  rw [one_div_one_div] at h
  linarith

noncomputable def strictEngelStep (s : ℝ × ℝ) : ℝ × ℝ :=
  let A := (strictEngelRatio s.1 s.2 : ℝ) * s.1
  (A, s.2 - 1 / (A - 1))

lemma strictEngelStep_remainder {n : ℕ} (hn : 1 ≤ n) :
    strictEngelStep ((n + 1).factorial, remainder n) =
      (((n + 2).factorial : ℝ), remainder (n + 1)) := by
  unfold strictEngelStep
  rw [strictEngelRatio_remainder hn]
  have hf : (n + 2 : ℝ) * (n + 1).factorial = (n + 2).factorial := by
    exact_mod_cast (Nat.factorial_succ (n + 1)).symm
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat, hf]
  rw [remainder_succ]
  rfl

lemma strictEngel_iterate_target (n : ℕ) :
    (strictEngelStep^[n]) (2, (∑' k : ℕ, term k) - 1) =
      (((n + 2).factorial : ℝ), remainder (n + 1)) := by
  induction n with
  | zero =>
    have ht : term 0 = 1 := by norm_num [term]
    simp [remainder, ht]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      strictEngelStep_remainder (show 1 ≤ n + 1 by omega)

#print axioms strictEngel_iterate_target


lemma strictEngelStep_pos {s : ℝ × ℝ} (hA : 0 < s.1) (hr : 0 < s.2) :
    0 < (strictEngelStep s).1 ∧ 0 < (strictEngelStep s).2 := by
  obtain ⟨hd, ht⟩ := strictEngel_step_pos hA hr
  constructor
  · change 0 < (strictEngelRatio s.1 s.2 : ℝ) * s.1
    linarith
  · exact ht

lemma strictEngel_iterate_pos {s : ℝ × ℝ} (hA : 0 < s.1) (hr : 0 < s.2)
    (n : ℕ) :
    0 < ((strictEngelStep^[n]) s).1 ∧ 0 < ((strictEngelStep^[n]) s).2 := by
  induction n with
  | zero => exact ⟨hA, hr⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact strictEngelStep_pos ih.1 ih.2

/-- A fixed rational starting state for which this strict algorithm never
terminates. This is not a counterexample to the conjecture in Spec.lean. -/
lemma strictEngel_rational_input_never_terminates (n : ℕ) :
    0 < ((strictEngelStep^[n]) (1, 1 / 4)).2 :=
  (strictEngel_iterate_pos (s := (1, 1 / 4)) (by norm_num) (by norm_num) n).2

#print axioms strictEngel_rational_input_never_terminates


#print axioms strictEngelRatio_remainder

end Erdos68Development
