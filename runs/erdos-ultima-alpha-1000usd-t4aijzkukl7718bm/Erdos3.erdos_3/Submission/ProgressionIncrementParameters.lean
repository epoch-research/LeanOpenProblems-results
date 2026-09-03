import Submission.QuadraticCorrelationProgressionIncrement
import Submission.BohrQuadraticFlattening

/-! Explicit, non-circular parameter choices for the progression density
increment. The final modulus threshold depends only on rank, length, and gain. -/
namespace Erdos3ProgressionIncrementParameters
open Finset Erdos3QuadraticCorrelationProgressionIncrement Erdos3BohrQuadraticFlattening
  Erdos3RelativeStableBohr Erdos3SimultaneousQuadraticRecurrence
open scoped Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

noncomputable def roundedScale (A r : ℝ) : ℕ := ⌈64*A/r⌉₊+1
lemma roundedScale_pos (A r : ℝ) : 0 < roundedScale A r := by unfold roundedScale; omega
lemma roundedScale_ratio (A : ℝ) {r : ℝ} (hr : 0 < r) :
    A/(roundedScale A r : ℝ) ≤ r/64 := by
  have hden : (0 : ℝ) < roundedScale A r := by exact_mod_cast roundedScale_pos A r
  have hh : 64*A/r ≤ (roundedScale A r : ℝ) := by
    apply (Nat.le_ceil _).trans
    simp only [roundedScale,Nat.cast_add,Nat.cast_one]
    linarith
  have hh' := (div_le_iff₀ hr).mp hh
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hh']

noncomputable def incrementPrecision (r : ℝ) : ℕ := roundedScale 1 r
noncomputable def incrementLinearMesh (L : ℕ) (r : ℝ) : ℕ := roundedScale (L : ℝ) r
noncomputable def incrementLocalLength (L : ℕ) (r : ℝ) : ℕ :=
  roundedScale (((2*incrementLinearMesh L r+1)^2 : ℕ)*(L : ℝ)) r
noncomputable def incrementAccuracy (L : ℕ) (r : ℝ) : ℕ :=
  flattenAccuracy (incrementLocalLength L r) (Nat.clog 2 (incrementPrecision r))
noncomputable def incrementCoarseLength (L : ℕ) (r : ℝ) : ℕ :=
  roundedScale ((recurrenceBound 1 (incrementAccuracy L r) : ℝ)*(incrementLocalLength L r : ℝ)) r
noncomputable def incrementCoarseMesh (D L : ℕ) (r : ℝ) : ℕ :=
  256*incrementCoarseLength L r*windowDenominator D (incrementPrecision r)+1
noncomputable def incrementTerminalCost (D L : ℕ) (r : ℝ) : ℕ :=
  (2*incrementCoarseMesh D L r+1)^(2*D)*incrementCoarseLength L r*257^(2*D)
noncomputable def incrementThreshold (D L : ℕ) (r : ℝ) : ℕ := roundedScale (incrementTerminalCost D L r : ℝ) r

lemma incrementPrecision_pos (r : ℝ) : 0 < incrementPrecision r := roundedScale_pos _ _
lemma incrementLinearMesh_pos (L : ℕ) (r : ℝ) : 0 < incrementLinearMesh L r := roundedScale_pos _ _
lemma incrementLocalLength_pos (L : ℕ) (r : ℝ) : 0 < incrementLocalLength L r := roundedScale_pos _ _
lemma incrementCoarseLength_pos (L : ℕ) (r : ℝ) : 0 < incrementCoarseLength L r := roundedScale_pos _ _
lemma incrementCoarseMesh_pos (D L : ℕ) (r : ℝ) : 0 < incrementCoarseMesh D L r := by
  unfold incrementCoarseMesh
  omega

lemma inverse_power_clog {m : ℕ} (hm : 0 < m) : (1/2 : ℝ)^(Nat.clog 2 m) ≤ 1/(m : ℝ) := by
  have hpow : (m : ℝ) ≤ (2 : ℝ)^(Nat.clog 2 m) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) m
  rw [div_pow,one_pow]
  exact div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hm) hpow

lemma increment_phase_error (L : ℕ) {r : ℝ} (hr : 0 < r) :
    partitionError (incrementLocalLength L r) L (incrementLinearMesh L r) (incrementAccuracy L r) ≤ r/16 := by
  have hpow := (inverse_power_clog (incrementPrecision_pos r)).trans (roundedScale_ratio 1 hr)
  have hquad := (flattenAccuracy_error (incrementLocalLength L r) (Nat.clog 2 (incrementPrecision r))).trans hpow
  have hlin := roundedScale_ratio (L : ℝ) hr
  change (L : ℝ)/(incrementLinearMesh L r : ℝ) ≤ r/64 at hlin
  change 2*(incrementLocalLength L r : ℝ)^2*(1/2 : ℝ)^(incrementAccuracy L r) ≤ r/64 at hquad
  unfold partitionError
  rw [show 2*(L : ℝ)/(incrementLinearMesh L r : ℝ) = 2*((L : ℝ)/(incrementLinearMesh L r : ℝ)) by ring]
  linarith only [hlin,hquad,hr]

lemma windowDenominator_mono {d D z : ℕ} (h : d ≤ D) : windowDenominator d z ≤ windowDenominator D z := by
  unfold windowDenominator
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 7 h) 1)

lemma increment_bohr_mesh {G : Type*} [AddCommGroup G] [Fintype G]
    (C : Finset (AddChar G ℂ)) {D : ℕ} (hC : C.card ≤ D) (L : ℕ) (r : ℝ)
    {R : ℝ} (hR : 1/64 ≤ R) :
    4*(incrementCoarseLength L r : ℝ)/(incrementCoarseMesh D L r : ℝ) ≤
      relativeWidth C (incrementPrecision r) R := by
  let W := windowDenominator D (incrementPrecision r)
  let W' := windowDenominator C.card (incrementPrecision r)
  have hW : (0 : ℝ) < W := by exact_mod_cast windowDenominator_pos D (incrementPrecision_pos r)
  have hW' : (0 : ℝ) < W' := by exact_mod_cast windowDenominator_pos C.card (incrementPrecision_pos r)
  have hWW : (W' : ℝ) ≤ W := by exact_mod_cast windowDenominator_mono hC
  have hn : (0 : ℝ) < incrementCoarseMesh D L r := by exact_mod_cast incrementCoarseMesh_pos D L r
  have hmesh : 4*(incrementCoarseLength L r : ℝ)/(incrementCoarseMesh D L r : ℝ) ≤ (1/64 : ℝ)/(W : ℝ) := by
    apply (div_le_div_iff₀ hn hW).mpr
    have he : (incrementCoarseMesh D L r : ℝ) = 256*(incrementCoarseLength L r : ℝ)*(W : ℝ)+1 := by
      simp only [incrementCoarseMesh,W,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    rw [he]
    nlinarith only []
  exact (hmesh.trans (div_le_div_of_nonneg_left (by norm_num) hW' hWW)).trans
    (div_le_div_of_nonneg_right hR hW'.le)

lemma increment_terminal_bound {d D p L : ℕ} (hd : d ≤ D) {r : ℝ} (hr : 0 < r)
    (hp : incrementThreshold D L r ≤ p) :
    (((2*incrementCoarseMesh D L r+1)^(2*d)*incrementCoarseLength L r*257^(2*d) : ℕ) : ℝ)/(p : ℝ) ≤ r/64 := by
  have hcost : (2*incrementCoarseMesh D L r+1)^(2*d)*incrementCoarseLength L r*257^(2*d) ≤
      incrementTerminalCost D L r := by
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 2 hd))
    · exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 2 hd)
  have hth : (0 : ℝ) < incrementThreshold D L r := by exact_mod_cast roundedScale_pos (incrementTerminalCost D L r : ℝ) r
  calc
    _ ≤ (incrementTerminalCost D L r : ℝ)/(p : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcost) (Nat.cast_nonneg _)
    _ ≤ (incrementTerminalCost D L r : ℝ)/(incrementThreshold D L r : ℝ) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hth (by exact_mod_cast hp)
    _ ≤ _ := roundedScale_ratio _ hr

lemma increment_partition_budget {d D p L : ℕ} (hd : d ≤ D) {r : ℝ} (hr : 0 < r)
    (hp : incrementThreshold D L r ≤ p) :
    partitionError (incrementLocalLength L r) L (incrementLinearMesh L r) (incrementAccuracy L r)+
      2*partitionLoss d p (incrementCoarseLength L r) (incrementLocalLength L r) L
        (incrementLinearMesh L r) (incrementCoarseMesh D L r) (incrementAccuracy L r) (incrementPrecision r) ≤ r/2 := by
  have he := increment_phase_error L hr
  have hterminal := increment_terminal_bound hd hr hp
  have hz := roundedScale_ratio 1 hr
  have hlocal := roundedScale_ratio (((2*incrementLinearMesh L r+1)^2 : ℕ)*(L : ℝ)) hr
  have hcoarse := roundedScale_ratio
    ((recurrenceBound 1 (incrementAccuracy L r) : ℝ)*(incrementLocalLength L r : ℝ)) hr
  change 1/(incrementPrecision r : ℝ) ≤ r/64 at hz
  change (((2*incrementLinearMesh L r+1)^2 : ℕ) : ℝ)*(L : ℝ)/(incrementLocalLength L r : ℝ) ≤ r/64 at hlocal
  change (recurrenceBound 1 (incrementAccuracy L r) : ℝ)*(incrementLocalLength L r : ℝ)/(incrementCoarseLength L r : ℝ) ≤ r/64 at hcoarse
  unfold partitionLoss
  linarith only [he,hterminal,hz,hlocal,hcoarse,hr]

#print axioms increment_partition_budget
#print axioms increment_bohr_mesh
end Erdos3ProgressionIncrementParameters
