import Submission.ContinuousIntervalQuantumBudget
import Submission.ContinuousIntervalQuantumReference

/-! A schedule-independent comparison budget for guarded integer-threshold
refinements, based on actual Jacobsthal lower bounds. No chord patches are
included and no quadratic positivity is asserted. -/
namespace Erdos970.ContinuousInterval
open Finset Real
set_option maxHeartbeats 2000000

lemma Regular.quantumRefine_dilation_of_zero {d : ℝ} {L U : ℝ → ℝ}
    (h : Regular d L U) (g n : ℕ) (hn : 0 < n) (hz : L (n : ℝ)=0) :
    Dominates (fun x => L (quantumDilationFactor (n+1)*x)/quantumDilationFactor (n+1))
      (fun x => U (quantumDilationFactor (n+1)*x)/quantumDilationFactor (n+1))
      (ContinuousInterval.quantumRefine d g L) U := by
  have hnn : 1 < n+1 := by omega
  have hc := quantumDilationFactor_one_le hnn
  unfold ContinuousInterval.quantumRefine
  split_ifs with hh
  · have hng : n < g := by
      by_contra hng
      have hm := h.lower_mono (show (g : ℝ) ≤ n by exact_mod_cast (show g ≤ n by omega))
      rw [hz] at hm
      exact hh.2.2.2.not_ge hm
    apply h.quantumPatch_dilation g hh.1 hh.2.1 hh.2.2.1 _ hc
    have hi := quantumDilationFactor_identity hnn
    have hgR : (n : ℝ)+1 ≤ g := by exact_mod_cast hng
    have hh := mul_nonneg (sub_nonneg.mpr hc)
      (show 0 ≤ (g : ℝ)-((n : ℝ)+1) by linarith)
    push_cast at hi
    nlinarith only [hi,hh]
  · exact h.dilation_self _ hc

/-- At a length strictly below h(k), the reference quantum lower envelope
vanishes for every schedule, including schedules with optional chord patches. -/
lemma quantumReference_zero_below_jacobsthal (cells : ℕ → List ℕ)
    (trigger : ℕ → ℕ) (k m : ℕ) (hm : m < jacobsthalFunction k) :
    (quantumEnvelope (fun i => (referenceMarginal i : ℝ)) cells trigger k).1 m=0 := by
  have hq (i : ℕ) : 0 ≤ (referenceMarginal i : ℝ) ∧ (referenceMarginal i : ℝ) ≤ 1 := by
    exact_mod_cast referenceMarginal_bounds i
  have hn := (quantumEnvelope_regular (fun i => (referenceMarginal i : ℝ))
    cells trigger k (fun i _ => hq i)).lower_nonneg (m : ℝ)
  apply le_antisymm _ hn
  by_contra hh
  have hp : 0 < (quantumEnvelope (fun i => (referenceMarginal i : ℝ)) cells trigger k).1 m := by linarith
  exact hm.not_ge (jacobsthalFunction_le_of_quantumReferencePositive cells trigger k m hp)

noncomputable def actualQuantumDilationBudget (k : ℕ) : ℝ :=
  quantumDilationBudget (fun i => jacobsthalFunction (i+1)) k

lemma actualQuantumDilationBudget_one_le (k : ℕ) :
    1 ≤ actualQuantumDilationBudget k :=
  quantumDilationBudget_one_le _ _ (fun i _ =>
    (by omega : 1 ≤ i+1).trans_lt (lt_jacobsthalFunction (i+1)))

lemma actualQuantumDilationBudget_succ (k : ℕ) :
    actualQuantumDilationBudget (k+1)=
      actualQuantumDilationBudget k*quantumDilationFactor (jacobsthalFunction (k+1)) := by
  simp only [actualQuantumDilationBudget,quantumDilationBudget,prod_range_succ]

lemma actualQuantumDilationBudget_mono : Monotone actualQuantumDilationBudget := by
  apply monotone_nat_of_le_succ
  intro k
  rw [actualQuantumDilationBudget_succ]
  have hB : 0 ≤ actualQuantumDilationBudget k := (by norm_num : (0 : ℝ) ≤ 1).trans
    (actualQuantumDilationBudget_one_le k)
  have hf := quantumDilationFactor_one_le ((by omega : 1 ≤ k+1).trans_lt (lt_jacobsthalFunction (k+1)))
  nlinarith only [mul_le_mul_of_nonneg_left hf hB]

/-- Every guarded schedule is dominated by the ordinary recursion at the
same actual-Jacobsthal comparison budget. This is not a positivity theorem. -/
theorem quantumReference_actual_dilation (trigger : ℕ → ℕ) (k : ℕ) :
    Dominates
      (fun x => (envelope (fun i => (referenceMarginal i : ℝ)) k
        (actualQuantumDilationBudget k*x)).1/actualQuantumDilationBudget k)
      (fun x => (envelope (fun i => (referenceMarginal i : ℝ)) k
        (actualQuantumDilationBudget k*x)).2/actualQuantumDilationBudget k)
      (quantumEnvelope (fun i => (referenceMarginal i : ℝ)) (fun _ => []) trigger k).1
      (quantumEnvelope (fun i => (referenceMarginal i : ℝ)) (fun _ => []) trigger k).2 := by
  let Q := fun i => (referenceMarginal i : ℝ)
  have hQ (i : ℕ) : 0 ≤ Q i ∧ Q i ≤ 1 := by
    dsimp only [Q]
    exact_mod_cast referenceMarginal_bounds i
  induction k with
  | zero =>
    constructor <;> intros <;>
      simp [actualQuantumDilationBudget,quantumDilationBudget,envelope,quantumEnvelope]
  | succ k ih =>
    let E := quantumEnvelope Q (fun _ => []) trigger k
    let n := jacobsthalFunction (k+1)-1
    have hJ : 1 < jacobsthalFunction (k+1) :=
      (by omega : 1 ≤ k+1).trans_lt (lt_jacobsthalFunction (k+1))
    have hn : 0 < n := by dsimp [n]; omega
    have hnJ : n+1=jacobsthalFunction (k+1) := by dsimp [n]; omega
    have hzero := quantumReference_zero_below_jacobsthal (fun _ => []) trigger (k+1) n
      (by dsimp [n]; omega)
    have hr := quantumEnvelope_regular Q (fun _ => []) trigger k (fun i _ => hQ i)
    have hs := hr.step (Q k) (hQ k).1 (hQ k).2
    have he : density Q k*(1-Q k)=density Q (k+1) := by
      simp only [density,prod_range_succ]
    rw [he] at hs
    have hprezero : stepLower (Q k) E.1 E.2 (n : ℝ)=0 := by
      have hdom := quantumRefine_dominates (density Q (k+1)) (trigger k)
        (stepLower (Q k) E.1 E.2) (stepUpper (Q k) E.1 E.2)
      have hh := hdom.1 (n : ℝ)
      change _ ≤ (quantumEnvelope Q (fun _ => []) trigger (k+1)).1 n at hh
      rw [hzero] at hh
      exact le_antisymm hh (hs.lower_nonneg _)
    have hpatch := hs.quantumRefine_dilation_of_zero (trigger k) n hn hprezero
    rw [hnJ] at hpatch
    have hd := actualQuantumDilationBudget_one_le k
    have hc := quantumDilationFactor_one_le hJ
    have hc0 : 0 < quantumDilationFactor (jacobsthalFunction (k+1)) := by linarith
    have hstep := ih.step (Q k) (hQ k).1 (hQ k).2
    have hscale := (envelope_regular Q k (fun i _ => hQ i)).dilation_step (Q k)
      (actualQuantumDilationBudget k) (hQ k).1 (hQ k).2 hd
    have hpre := (hscale.trans hstep).dilate (quantumDilationFactor (jacobsthalFunction (k+1))) hc0
    have hall := hpre.trans hpatch
    simpa only [quantumEnvelope,chordPatches,actualQuantumDilationBudget_succ,
      envelope,E,Q,mul_assoc,div_div] using hall

#print axioms quantumReference_actual_dilation
end Erdos970.ContinuousInterval
