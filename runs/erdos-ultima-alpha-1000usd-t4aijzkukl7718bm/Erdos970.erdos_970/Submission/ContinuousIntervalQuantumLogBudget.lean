import Submission.ContinuousIntervalQuantumActualBudget
import Submission.EventualLowerAsymptotic

/-! Guarded integer-threshold refinements have a schedule-independent
comparison budget smaller than every fixed positive power of log k.
This is a comparison result, not an endpoint positivity theorem. -/
namespace Erdos970.ContinuousInterval
open Finset Real Filter
set_option maxHeartbeats 2000000

lemma reciprocal_log_step (x : ℝ) (hx : 1 < x) :
    1/((x+1)*log (x+1)) ≤ log (log (x+1))-log (log x) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x+1 := by linarith
  have hlx : 0 < log x := log_pos hx
  have hlx1 : 0 < log (x+1) := log_pos (by linarith)
  have h1 := one_sub_inv_le_log_of_pos (div_pos hx1 hx0)
  rw [log_div hx1.ne' hx0.ne'] at h1
  have he1 : 1-((x+1)/x)⁻¹=1/(x+1) := by field_simp; ring
  rw [he1] at h1
  have h2 := one_sub_inv_le_log_of_pos (div_pos hlx1 hlx)
  rw [log_div hlx1.ne' hlx.ne'] at h2
  have he2 : 1-(log (x+1)/log x)⁻¹=(log (x+1)-log x)/log (x+1) := by field_simp
  rw [he2] at h2
  apply le_trans _ h2
  have hh := div_le_div_of_nonneg_right h1 hlx1.le
  simpa only [one_div_mul_one_div,div_div] using hh

lemma eventually_reciprocal_jacobsthal_log_step (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i : ℕ in atTop,
      2/((jacobsthalFunction (i+1) : ℝ)-1) ≤
        ε*(log (log ((i+1 : ℕ) : ℝ))-log (log (i : ℝ))) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (ConstructiveCover.eventually_any_mul_log_lt_jacobsthalFunction (4/ε) (by positivity))
  filter_upwards [eventually_ge_atTop (max N 2)] with i hi
  have hi2 : 2 ≤ i := (le_max_right _ _).trans hi
  have hin : N ≤ i+1 := by have := (le_max_left _ _).trans hi; omega
  have hb := hN (i+1) hin
  have hJ : 2 ≤ jacobsthalFunction (i+1) := by have := lt_jacobsthalFunction (i+1); omega
  have hJR : (2 : ℝ) ≤ jacobsthalFunction (i+1) := by exact_mod_cast hJ
  have hi0 : (0 : ℝ) < (i+1 : ℕ) := by positivity
  have hlog : 0 < log ((i+1 : ℕ) : ℝ) := log_pos (by exact_mod_cast (show 1 < i+1 by omega))
  have hB : 0 < ((jacobsthalFunction (i+1) : ℝ)-1) := by linarith
  have hnum : 2*((i+1 : ℕ) : ℝ)*log ((i+1 : ℕ) : ℝ) ≤
      ε*((jacobsthalFunction (i+1) : ℝ)-1) := by
    have hh := mul_lt_mul_of_pos_left hb hε
    have he : ε*(4/ε*((i+1 : ℕ) : ℝ)*log ((i+1 : ℕ) : ℝ))=
        4*((i+1 : ℕ) : ℝ)*log ((i+1 : ℕ) : ℝ) := by field_simp
    rw [he] at hh
    have hhalf := mul_le_mul_of_nonneg_left
      (show (jacobsthalFunction (i+1) : ℝ)/2 ≤ (jacobsthalFunction (i+1) : ℝ)-1 by linarith) hε.le
    nlinarith only [hh,hhalf]
  have hrec : 2/((jacobsthalFunction (i+1) : ℝ)-1) ≤
      ε/(((i+1 : ℕ) : ℝ)*log ((i+1 : ℕ) : ℝ)) := by
    apply (div_le_div_iff₀ hB (mul_pos hi0 hlog)).mpr
    nlinarith only [hnum]
  have hs := mul_le_mul_of_nonneg_left (reciprocal_log_step (i : ℝ)
    (by exact_mod_cast hi2)) hε.le
  apply hrec.trans
  simpa only [Nat.cast_add,Nat.cast_one,mul_one_div] using hs

/-- An eventual logarithmic envelope for the actual-Jacobsthal product. -/
theorem actualQuantumDilationBudget_eventually_log (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      actualQuantumDilationBudget k ≤ C*(log (k : ℝ))^ε := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_reciprocal_jacobsthal_log_step ε hε)
  let T := max N 2
  have hT2 : 2 ≤ T := le_max_right _ _
  have hBT : 0 < actualQuantumDilationBudget T := lt_of_lt_of_le (by norm_num)
    (actualQuantumDilationBudget_one_le T)
  let C := actualQuantumDilationBudget T*exp (-ε*log (log (T : ℝ)))
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : ∀ k, T ≤ k → actualQuantumDilationBudget k ≤ C*exp (ε*log (log (k : ℝ))) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      dsimp only [C]
      rw [mul_assoc,← exp_add]
      simp
    | succ k hk ih =>
      have hkN : N ≤ k := (le_max_left _ _).trans hk
      have hJ : 1 < jacobsthalFunction (k+1) :=
        (by omega : 1 ≤ k+1).trans_lt (lt_jacobsthalFunction (k+1))
      have hf : quantumDilationFactor (jacobsthalFunction (k+1)) ≤
          exp (ε*(log (log ((k+1 : ℕ) : ℝ))-log (log (k : ℝ)))) := by
        rw [quantumDilationFactor_eq_one_add hJ]
        apply le_trans _ (exp_le_exp.mpr (hN k hkN))
        simpa only [add_comm] using add_one_le_exp (2/((jacobsthalFunction (k+1) : ℝ)-1))
      rw [actualQuantumDilationBudget_succ]
      apply (mul_le_mul ih hf (by linarith only [quantumDilationFactor_one_le hJ]) (by positivity)).trans_eq
      rw [mul_assoc,← exp_add]
      congr 2
      ring
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop T] with k hk
  have hlog : 0 < log (k : ℝ) := log_pos (by exact_mod_cast (hT2.trans hk))
  have hh := hbound k hk
  rw [rpow_def_of_pos hlog ε]
  simpa only [mul_comm ε (log (log (k : ℝ)))] using hh

/-- Uniform in every stage, after absorbing finitely many stages. The
constant depends on epsilon, not on the guarded trigger schedule. -/
theorem actualQuantumDilationBudget_log_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ k : ℕ,
      actualQuantumDilationBudget k ≤ C*(log ((k : ℝ)+2))^ε := by
  obtain ⟨C,hC,he⟩ := actualQuantumDilationBudget_eventually_log ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let B := actualQuantumDilationBudget N
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) (actualQuantumDilationBudget_one_le N)
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  let A := C+B/(log (2 : ℝ))^ε
  have hA : 0 < A := by dsimp [A]; positivity
  have hCA : C ≤ A := by dsimp [A]; exact le_add_of_nonneg_right (by positivity)
  refine ⟨A,hA,fun k => ?_⟩
  by_cases hk : N ≤ k
  · apply (hN k hk).trans
    apply mul_le_mul (by exact hCA) _ (rpow_nonneg (log_natCast_nonneg k) ε) hA.le
    apply rpow_le_rpow (log_natCast_nonneg k) _ hε.le
    by_cases hk0 : k=0
    · subst k; simp; exact hlog2.le
    · exact log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hk0) (by linarith)
  · have hBN : actualQuantumDilationBudget k ≤ B := actualQuantumDilationBudget_mono (by omega)
    have hpow : (log (2 : ℝ))^ε ≤ (log ((k : ℝ)+2))^ε := by
      apply rpow_le_rpow hlog2.le _ hε.le
      exact log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
    have hBA : B ≤ A*(log (2 : ℝ))^ε := by
      dsimp only [A]
      rw [add_mul,div_mul_cancel₀ _ (rpow_pos_of_pos hlog2 ε).ne']
      exact le_add_of_nonneg_left (by positivity)
    exact hBN.trans (hBA.trans (mul_le_mul_of_nonneg_left hpow hA.le))

lemma Regular.dilation_mono {d : ℝ} {L U : ℝ → ℝ} (h : Regular d L U)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Dominates (fun x => L (b*x)/b) (fun x => U (b*x)/b)
      (fun x => L (a*x)/a) (fun x => U (a*x)/a) := by
  have hc : 1 ≤ b/a := (le_div_iff₀ ha).mpr (by simpa using hab)
  have hh := (h.dilation_self (b/a) hc).dilate a ha
  have he : b/a*a=b := div_mul_cancel₀ b ha.ne'
  simpa only [← mul_assoc,div_div,he] using hh

/-- Every guarded schedule is dominated by one dilation of size
C_epsilon * log(k+2)^epsilon. The comparison is simultaneous in all lengths
and in all schedules, but does not include later chord patches. -/
theorem quantumReference_log_dilation (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ trigger : ℕ → ℕ, ∀ k : ℕ,
      Dominates
        (fun x => (envelope (fun i => (referenceMarginal i : ℝ)) k
          ((C*log ((k : ℝ)+2)^ε)*x)).1/(C*log ((k : ℝ)+2)^ε))
        (fun x => (envelope (fun i => (referenceMarginal i : ℝ)) k
          ((C*log ((k : ℝ)+2)^ε)*x)).2/(C*log ((k : ℝ)+2)^ε))
        (quantumEnvelope (fun i => (referenceMarginal i : ℝ)) (fun _ => []) trigger k).1
        (quantumEnvelope (fun i => (referenceMarginal i : ℝ)) (fun _ => []) trigger k).2 := by
  obtain ⟨C,hC,hbound⟩ := actualQuantumDilationBudget_log_bound ε hε
  refine ⟨C,hC,fun trigger k => ?_⟩
  have hr := envelope_regular (fun i => (referenceMarginal i : ℝ)) k (fun i _ => by
    change 0 ≤ (referenceMarginal i : ℝ) ∧ (referenceMarginal i : ℝ) ≤ 1
    exact_mod_cast referenceMarginal_bounds i)
  have hB : 0 < actualQuantumDilationBudget k := lt_of_lt_of_le (by norm_num)
    (actualQuantumDilationBudget_one_le k)
  exact (hr.dilation_mono _ _ hB (hbound k)).trans (quantumReference_actual_dilation trigger k)

#print axioms actualQuantumDilationBudget_log_bound
#print axioms quantumReference_log_dilation
end Erdos970.ContinuousInterval
