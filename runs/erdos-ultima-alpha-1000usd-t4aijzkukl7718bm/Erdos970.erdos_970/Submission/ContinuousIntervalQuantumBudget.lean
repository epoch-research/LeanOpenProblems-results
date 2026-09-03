import Submission.ContinuousIntervalQuantumDilation

/-! A guarded quantum refinement never changes a zero at a natural length.
This bounds the cumulative dilation for arbitrary trigger schedules, without
assuming those schedules are successful. No chord refinements are inserted in
the comparison with the ordinary recurrence. -/
namespace Erdos970.ContinuousInterval

lemma Regular.quantumRefine_zero_nat {d : ℝ} {L U : ℝ → ℝ}
    (h : Regular d L U) (g n : ℕ) (hz : L (n : ℝ) = 0) :
    ContinuousInterval.quantumRefine d g L n = 0 := by
  unfold ContinuousInterval.quantumRefine
  split_ifs with hh
  · have hng : n < g := by
      by_contra hn
      have hgn : (g : ℝ) ≤ n := by exact_mod_cast (show g ≤ n by omega)
      have hm := h.lower_mono hgn
      rw [hz] at hm
      exact hh.2.2.2.not_ge hm
    have hnR : (n : ℝ) ≤ (g : ℝ) - 1 := by
      have : (n : ℝ) + 1 ≤ g := by exact_mod_cast hng
      linarith
    rw [quantumPatch_eq_left_of_le g hh.1
      (h.quantumIntercept_nonpos g hh.2.1 hh.2.2.1)
      (h.quantumSlope_bounds g).1 h.lower_nonneg n hnR]
    exact hz
  · exact hz

lemma Regular.stepLower_zero_succ {d : ℝ} {L U : ℝ → ℝ}
    (h : Regular d L U) (n : ℕ) (hz : L (n : ℝ) = 0) (q : ℝ) (hq : 0 ≤ q) :
    stepLower q L U (n + 1 : ℕ) = 0 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hl := h.lower_lip (n : ℝ) ((n : ℝ) + 1) (by linarith)
  rw [hz] at hl
  have hu := h.upper_growth 0 1 (by norm_num) (by norm_num)
  rw [h.upper_zero] at hu
  have harg : 1 ≤ upperArg q ((n : ℝ) + 1) := by
    unfold upperArg
    nlinarith [mul_nonneg hn hq]
  have hum := h.upper_mono (by norm_num : (0 : ℝ) ≤ 1)
    (show 0 ≤ upperArg q ((n : ℝ) + 1) by linarith) harg
  simp only [stepLower, clip, Nat.cast_add, Nat.cast_one,
    max_eq_right (show 0 ≤ (n : ℝ) + 1 by positivity)]
  dsimp only [upperArg] at hum
  simp only [sub_zero, add_sub_cancel_left, mul_one] at hl hu
  exact max_eq_left (by linarith)

/-- The stage index is always a natural-length zero, even after guarded quantum
refinements. This does not give an upper bound on the first positive length. -/
theorem quantumEnvelope_zero_at_stage (Q : ℕ → ℝ) (trigger : ℕ → ℕ) (k : ℕ)
    (hQ : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1) :
    (quantumEnvelope Q (fun _ => []) trigger k).1 k = 0 := by
  induction k with
  | zero => simp [quantumEnvelope]
  | succ k ih =>
    have hQQ : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1 := fun i hi => hQ i (by omega)
    have hqk := hQ k (by omega)
    have hr := quantumEnvelope_regular Q (fun _ => []) trigger k hQQ
    have hz := hr.stepLower_zero_succ k (ih hQQ) (Q k) hqk.1
    have hs := hr.step (Q k) hqk.1 hqk.2
    have he : density Q k * (1 - Q k) = density Q (k + 1) := by
      simp only [density, Finset.prod_range_succ]
    rw [he] at hs
    exact hs.quantumRefine_zero_nat (trigger k) (k + 1) hz

/-- A trigger at or below a known natural zero cannot pass the guard. Thus its
cost may safely be replaced by the cost at the next natural length. -/
theorem Regular.quantumRefine_safe_dilation {d : ℝ} {L U : ℝ → ℝ}
    (h : Regular d L U) (g n : ℕ) (hn : 0 < n) (hz : L (n : ℝ) = 0) :
    let c := quantumDilationFactor (max g (n + 1))
    Dominates (fun x => L (c * x) / c) (fun x => U (c * x) / c)
      (ContinuousInterval.quantumRefine d g L) U := by
  dsimp only
  by_cases hng : n < g
  · rw [max_eq_left (show n + 1 ≤ g by omega)]
    exact h.quantumRefine_dilation g (by omega)
  · have hbad : ¬(0 < d ∧ 0 < g ∧ L ((g - 1 : ℕ) : ℝ) = 0 ∧ 0 < L g) := by
      intro hh
      have hgn : (g : ℝ) ≤ n := by exact_mod_cast (show g ≤ n by omega)
      have hm := h.lower_mono hgn
      rw [hz] at hm
      exact hh.2.2.2.not_ge hm
    rw [ContinuousInterval.quantumRefine, if_neg hbad]
    exact h.dilation_self _ (quantumDilationFactor_one_le
      (by omega : 1 < max g (n + 1)))

noncomputable def safeQuantumDilationBudget (trigger : ℕ → ℕ) (k : ℕ) : ℝ :=
  quantumDilationBudget (fun i => max (trigger i) (i + 2)) k

lemma safeQuantumDilationBudget_bounds (trigger : ℕ → ℕ) (k : ℕ) :
    1 ≤ safeQuantumDilationBudget trigger k ∧
      safeQuantumDilationBudget trigger k ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 := by
  exact ⟨quantumDilationBudget_one_le _ _ (fun i _ => by omega),
    quantumDilationBudget_le_polynomial _ _ (fun i _ => le_max_right _ _)⟩

/-- Arbitrary guarded trigger schedules have an explicit, at-most-quadratic
cumulative dilation budget. The quantum recurrence itself is NOT changed or
clamped: only the comparison budget uses the maximum with `i+2`. -/
theorem quantumEnvelope_safe_dilation_budget (Q : ℕ → ℝ) (trigger : ℕ → ℕ) (k : ℕ)
    (hQ : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1) :
    Dominates (fun x => (envelope Q k (safeQuantumDilationBudget trigger k * x)).1 /
        safeQuantumDilationBudget trigger k)
      (fun x => (envelope Q k (safeQuantumDilationBudget trigger k * x)).2 /
        safeQuantumDilationBudget trigger k)
      (quantumEnvelope Q (fun _ => []) trigger k).1
      (quantumEnvelope Q (fun _ => []) trigger k).2 := by
  induction k with
  | zero =>
    constructor <;> intros <;> simp [safeQuantumDilationBudget,
      quantumDilationBudget, envelope, quantumEnvelope]
  | succ k ih =>
    have hQQ : ∀ i < k, 0 ≤ Q i ∧ Q i ≤ 1 := fun i hi => hQ i (by omega)
    have hqk := hQ k (by omega)
    have hd := (safeQuantumDilationBudget_bounds trigger k).1
    have htk : 1 < max (trigger k) (k + 2) := by omega
    have hc := quantumDilationFactor_one_le htk
    have hc0 : 0 < quantumDilationFactor (max (trigger k) (k + 2)) := by linarith
    let E := quantumEnvelope Q (fun _ => []) trigger k
    have hstep := (ih hQQ).step (Q k) hqk.1 hqk.2
    have hscale := (envelope_regular Q k hQQ).dilation_step (Q k)
      (safeQuantumDilationBudget trigger k) hqk.1 hqk.2 hd
    have hpre := (hscale.trans hstep).dilate
      (quantumDilationFactor (max (trigger k) (k + 2))) hc0
    have hr := quantumEnvelope_regular Q (fun _ => []) trigger k hQQ
    have hz := hr.stepLower_zero_succ k (quantumEnvelope_zero_at_stage Q trigger k hQQ)
      (Q k) hqk.1
    have hs := hr.step (Q k) hqk.1 hqk.2
    have he : density Q k * (1 - Q k) = density Q (k + 1) := by
      simp only [density, Finset.prod_range_succ]
    rw [he] at hs
    have hpatch := hs.quantumRefine_safe_dilation (trigger k) (k + 1) (by omega) hz
    have hall := hpre.trans hpatch
    have hbudget : safeQuantumDilationBudget trigger (k + 1) =
        safeQuantumDilationBudget trigger k * quantumDilationFactor (max (trigger k) (k + 2)) := by
      simp only [safeQuantumDilationBudget, quantumDilationBudget, Finset.prod_range_succ]
    simpa only [quantumEnvelope, chordPatches, hbudget, envelope, E,
      Nat.add_assoc, Nat.reduceAdd, mul_assoc, div_div] using hall

#print axioms quantumEnvelope_zero_at_stage
#print axioms safeQuantumDilationBudget_bounds
#print axioms quantumEnvelope_safe_dilation_budget
end Erdos970.ContinuousInterval
