import Submission.ContinuousIntervalQuantumBudget

/-! Exact comparison products charge only successful guarded refinements.
No chord patches are included. No positivity conclusion is assumed. -/
namespace Erdos970.ContinuousInterval
open Finset Real
set_option maxHeartbeats 1500000

noncomputable def quantumPreLower (Q : ℕ → ℝ) (trigger : ℕ → ℕ) (k : ℕ) : ℝ → ℝ :=
  let E := quantumEnvelope Q (fun _ => []) trigger k
  stepLower (Q k) E.1 E.2

/-- Exactly the guard used by the unchorded recursion, before refinement. -/
def quantumTriggerActive (Q : ℕ → ℝ) (trigger : ℕ → ℕ) (k : ℕ) : Prop :=
  0 < density Q (k+1) ∧ 0 < trigger k ∧
    quantumPreLower Q trigger k ((trigger k-1 : ℕ) : ℝ)=0 ∧
    0 < quantumPreLower Q trigger k (trigger k)

lemma quantumPreLower_regular (Q : ℕ → ℝ) (trigger : ℕ → ℕ) (k : ℕ)
    (hQ : ∀ i, 0 ≤ Q i ∧ Q i ≤ 1) :
    Regular (density Q (k+1)) (quantumPreLower Q trigger k)
      (stepUpper (Q k) (quantumEnvelope Q (fun _ => []) trigger k).1
        (quantumEnvelope Q (fun _ => []) trigger k).2) := by
  have hh := (quantumEnvelope_regular Q (fun _ => []) trigger k
    (fun i _ => hQ i)).step (Q k) (hQ k).1 (hQ k).2
  simpa only [density,prod_range_succ,quantumPreLower] using hh

lemma quantumPreLower_zero_at_stage (Q : ℕ → ℝ) (trigger : ℕ → ℕ) (k : ℕ)
    (hQ : ∀ i, 0 ≤ Q i ∧ Q i ≤ 1) :
    quantumPreLower Q trigger k (k+1 : ℕ)=0 :=
  (quantumEnvelope_regular Q (fun _ => []) trigger k (fun i _ => hQ i)).stepLower_zero_succ k
    (quantumEnvelope_zero_at_stage Q trigger k (fun i _ => hQ i)) (Q k) (hQ k).1

lemma quantumTriggerActive_gt_stage (Q : ℕ → ℝ) (trigger : ℕ → ℕ) (k : ℕ)
    (hQ : ∀ i, 0 ≤ Q i ∧ Q i ≤ 1) (h : quantumTriggerActive Q trigger k) :
    k+1 < trigger k := by
  by_contra hh
  have hm := (quantumPreLower_regular Q trigger k hQ).lower_mono
    (show (trigger k : ℝ) ≤ (k+1 : ℕ) by exact_mod_cast (show trigger k ≤ k+1 by omega))
  rw [quantumPreLower_zero_at_stage Q trigger k hQ] at hm
  exact h.2.2.2.not_ge hm

noncomputable def effectiveQuantumFactor (Q : ℕ → ℝ) (trigger : ℕ → ℕ) (k : ℕ) : ℝ := by
  classical
  exact if quantumTriggerActive Q trigger k then quantumDilationFactor (trigger k) else 1

lemma effectiveQuantumFactor_one_le (Q : ℕ → ℝ) (trigger : ℕ → ℕ) (k : ℕ)
    (hQ : ∀ i, 0 ≤ Q i ∧ Q i ≤ 1) : 1 ≤ effectiveQuantumFactor Q trigger k := by
  unfold effectiveQuantumFactor
  split_ifs with hh
  · have hg := quantumTriggerActive_gt_stage Q trigger k hQ hh
    exact quantumDilationFactor_one_le (by omega)
  · rfl

lemma effectiveQuantumFactor_le_three (Q : ℕ → ℝ) (trigger : ℕ → ℕ) (k : ℕ)
    (hQ : ∀ i, 0 ≤ Q i ∧ Q i ≤ 1) : effectiveQuantumFactor Q trigger k ≤ 3 := by
  unfold effectiveQuantumFactor
  split_ifs with hh
  · have hg := quantumTriggerActive_gt_stage Q trigger k hQ hh
    have hgR : (2 : ℝ) ≤ trigger k := by exact_mod_cast (show 2 ≤ trigger k by omega)
    rw [quantumDilationFactor_eq_one_add (by omega : 1 < trigger k)]
    have hd : 2/((trigger k : ℝ)-1) ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    linarith
  · norm_num

noncomputable def effectiveQuantumDilationBudget (Q : ℕ → ℝ) (trigger : ℕ → ℕ) (k : ℕ) : ℝ :=
  ∏ i ∈ range k, effectiveQuantumFactor Q trigger i

lemma effectiveQuantumDilationBudget_one_le (Q : ℕ → ℝ) (trigger : ℕ → ℕ) (k : ℕ)
    (hQ : ∀ i, 0 ≤ Q i ∧ Q i ≤ 1) : 1 ≤ effectiveQuantumDilationBudget Q trigger k := by
  unfold effectiveQuantumDilationBudget
  calc
    1 = ∏ _i ∈ range k, (1 : ℝ) := by simp
    _ ≤ _ := prod_le_prod (fun _ _ => by norm_num)
      (fun i hi => effectiveQuantumFactor_one_le Q trigger i hQ)

lemma quantumPreLower_effective_dilation (Q : ℕ → ℝ) (trigger : ℕ → ℕ) (k : ℕ)
    (hQ : ∀ i, 0 ≤ Q i ∧ Q i ≤ 1) :
    let E := quantumEnvelope Q (fun _ => []) trigger k
    let c := effectiveQuantumFactor Q trigger k
    Dominates
      (fun x => quantumPreLower Q trigger k (c*x)/c)
      (fun x => stepUpper (Q k) E.1 E.2 (c*x)/c)
      (quantumEnvelope Q (fun _ => []) trigger (k+1)).1
      (quantumEnvelope Q (fun _ => []) trigger (k+1)).2 := by
  dsimp only
  by_cases hh : quantumTriggerActive Q trigger k
  · rw [effectiveQuantumFactor,if_pos hh]
    have hg := quantumTriggerActive_gt_stage Q trigger k hQ hh
    exact (quantumPreLower_regular Q trigger k hQ).quantumRefine_dilation
      (trigger k) (by omega)
  · have he : (quantumEnvelope Q (fun _ => []) trigger (k+1)).1 =
        quantumPreLower Q trigger k := by
      change ContinuousInterval.quantumRefine (density Q (k+1)) (trigger k)
        (quantumPreLower Q trigger k) = _
      unfold ContinuousInterval.quantumRefine
      exact if_neg hh
    rw [effectiveQuantumFactor,if_neg hh,he]
    constructor <;> intros <;> simp only [one_mul,div_one] <;> exact le_rfl

/-- The exact successful-trigger product compares the complete recursion,
including all failures of the guard, with one ordinary-envelope dilation. -/
theorem quantumEnvelope_effective_dilation (Q : ℕ → ℝ) (trigger : ℕ → ℕ) (k : ℕ)
    (hQ : ∀ i, 0 ≤ Q i ∧ Q i ≤ 1) :
    let B := effectiveQuantumDilationBudget Q trigger k
    Dominates (fun x => (envelope Q k (B*x)).1/B)
      (fun x => (envelope Q k (B*x)).2/B)
      (quantumEnvelope Q (fun _ => []) trigger k).1
      (quantumEnvelope Q (fun _ => []) trigger k).2 := by
  dsimp only
  induction k with
  | zero =>
    constructor <;> intros <;> simp [effectiveQuantumDilationBudget,envelope,quantumEnvelope]
  | succ k ih =>
    have hB := effectiveQuantumDilationBudget_one_le Q trigger k hQ
    have hf := effectiveQuantumFactor_one_le Q trigger k hQ
    have hf0 : 0 < effectiveQuantumFactor Q trigger k := by linarith
    have hstep := ih.step (Q k) (hQ k).1 (hQ k).2
    have hscale := (envelope_regular Q k (fun i _ => hQ i)).dilation_step (Q k)
      (effectiveQuantumDilationBudget Q trigger k) (hQ k).1 (hQ k).2 hB
    have hpre := (hscale.trans hstep).dilate (effectiveQuantumFactor Q trigger k) hf0
    have hall := hpre.trans (quantumPreLower_effective_dilation Q trigger k hQ)
    have he : effectiveQuantumDilationBudget Q trigger (k+1)=
        effectiveQuantumDilationBudget Q trigger k*effectiveQuantumFactor Q trigger k := by
      simp only [effectiveQuantumDilationBudget,prod_range_succ]
    simpa only [envelope,he,mul_assoc,div_div] using hall

#print axioms quantumEnvelope_effective_dilation
#print axioms effectiveQuantumFactor_le_three
end Erdos970.ContinuousInterval
