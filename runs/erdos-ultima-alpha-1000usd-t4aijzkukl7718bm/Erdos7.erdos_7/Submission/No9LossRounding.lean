import Submission.No9OperatorRounding

/-! Rounding soundness for losses and mass-dependent grid pruning. -/
namespace Erdos7No9Certificate
open scoped BigOperators
open Erdos7KilledSieve Erdos7Distortion
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

structure LossGeometry (A B q j : ℕ) : Prop where
  B_pos : 0 < B
  B_le_A : B ≤ A
  q_pos : 0 < q
  index_lt : j+1 < nodes
  lower : A*grid j ≤ q*(A-B)
  upper : q*(A-B) ≤ A*grid (j+1)

lemma loss_geometry (A B q j : ℕ) (hv : LossGeometry A B q j) :
    realGrid (gridIndex j) < realGrid (gridIndex (j+1)) ∧
    realGrid (gridIndex j) ≤ (q:ℚ)*(A-B)/A ∧
    (q:ℚ)*(A-B)/A ≤ realGrid (gridIndex (j+1)) := by
  have hA : (0:ℚ) < A := by exact_mod_cast (hv.B_pos.trans_le hv.B_le_A)
  have hl : (A:ℚ)*grid j ≤ q*(A-B) := by
    simpa only [Nat.cast_sub hv.B_le_A] using
      (show (A:ℚ)*grid j ≤ q*((A-B:ℕ):ℚ) from by exact_mod_cast hv.lower)
  have hu : (q:ℚ)*(A-B) ≤ A*grid (j+1) := by
    simpa only [Nat.cast_sub hv.B_le_A] using
      (show (q:ℚ)*((A-B:ℕ):ℚ) ≤ A*grid (j+1) from by exact_mod_cast hv.upper)
  simp only [realGrid,gridIndex_val _ (by have := hv.index_lt; omega : j < nodes),
    gridIndex_val _ hv.index_lt]
  refine ⟨by exact_mod_cast grid_succ j hv.index_lt,?_,?_⟩
  · exact (le_div_iff₀ hA).mpr (by nlinarith only [hl])
  · exact (div_le_iff₀ hA).mpr (by nlinarith only [hu])

lemma rounded_loss_chord (A B q j : ℕ) (hv : LossGeometry A B q j) (h : ℕ → ℕ) :
    ((A:ℚ)/B)*(1/q)*gridChord realGrid (gridIndex j) (gridIndex (j+1))
      ((q:ℚ)*(A-B)/A) (realValues h) ≤
    (ceilDiv ((A*grid (j+1)-q*(A-B))*h j+(q*(A-B)-A*grid j)*h (j+1))
      (B*q*(grid (j+1)-grid j)):ℚ)/scale := by
  have hA : (A:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt (hv.B_pos.trans_le hv.B_le_A))
  have hB : (B:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hv.B_pos)
  have hq : (q:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hv.q_pos)
  have hg := grid_succ j hv.index_lt
  have hwidth : 0 < grid (j+1)-grid j := Nat.sub_pos_of_lt hg
  have hden : 0 < B*q*(grid (j+1)-grid j) := Nat.mul_pos (Nat.mul_pos hv.B_pos hv.q_pos) hwidth
  have hwQ : (grid (j+1):ℚ)-grid j≠0 := by
    have hh : (grid j:ℚ) < grid (j+1) := by exact_mod_cast hg
    linarith
  have hh := div_le_div_of_nonneg_right (ceilDiv_bound
    ((A*grid (j+1)-q*(A-B))*h j+(q*(A-B)-A*grid j)*h (j+1))
    (B*q*(grid (j+1)-grid j)) hden) scale_pos.le
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hv.upper,Nat.cast_sub hv.lower,
    Nat.cast_sub hv.B_le_A,Nat.cast_sub hg.le] at hh
  convert hh using 1
  simp only [gridChord,realGrid,realValues,gridIndex_val _ (by have := hv.index_lt; omega : j < nodes),
    gridIndex_val _ hv.index_lt]
  field_simp

lemma rounded_prefix_loss (a : PrefixControl)
    (hv : LossGeometry a.A a.B (denominator a.p) a.lossIndex) (h : ℕ → ℕ) :
    ((a.A:ℚ)/a.B)*(1/(denominator a.p:ℚ))*
      gridChord realGrid (gridIndex a.lossIndex) (gridIndex (a.lossIndex+1))
        ((denominator a.p:ℚ)*(a.A-a.B)/a.A) (realValues h) ≤ (loss a h:ℚ)/scale :=
  rounded_loss_chord _ _ _ _ hv h

lemma loss_threshold_identity (A B q : ℕ) (hA : 0 < A) (hB : 0 < B) (hq : 0 < q) :
    ((A:ℚ)/B)*(1/q)*((q:ℚ)*(A-B)/A)=(A:ℚ)/B-1 := by
  have hAq : (A:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hA)
  have hBq : (B:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hqq : (q:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  field_simp

def pruneValues (h : ℕ → ℕ) (b m j : ℕ) : ℕ :=
  if j ≤ b then min (h j) (h b+(grid b-grid j)*m) else h j

section Grid
variable {n : ℕ} (κ : Type*) (A : Fin n → Type*)
variable [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]

lemma completeGridBound_rounded_loss (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (h : ℕ → ℕ) (hh : CompleteGridBound κ A E c q t μ realGrid (realValues h))
    (a : PrefixControl) (hv : LossGeometry a.A a.B (denominator a.p) a.lossIndex) :
    CompleteTestBound κ A E c q t μ 1
      (fun z => residual ((a.A:ℚ)/a.B) ((1/(denominator a.p:ℚ))*z)) ((loss a h:ℚ)/scale) := by
  obtain ⟨hlr,hlu,hur⟩ := loss_geometry _ _ _ _ hv
  have hb := completeGridBound_chord κ A E c q t μ hμ _ _ hh _ _ _ hlr hlu hur
  have hr := completeHingeBound_residual κ A E c q t μ _ _ hb ((a.A:ℚ)/a.B)
    (1/(denominator a.p:ℚ)) (by positivity) (by positivity)
    (loss_threshold_identity _ _ _ (hv.B_pos.trans_le hv.B_le_A) hv.B_pos hv.q_pos)
  exact completeTestBound_mono κ A E c q t μ 1 _ hr (rounded_prefix_loss a hv h)

lemma completeGridBound_pruneValues (E : Fin n → ℕ) (c : Fin n → ℚ)
    (q : Fin n → ℕ → ℚ) (t : ℕ) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (h : ℕ → ℕ) (hh : CompleteGridBound κ A E c q t μ realGrid (realValues h))
    (b m : ℕ) (hb : b < nodes) (hm : (∑ x,μ x)=(m:ℚ)/scale) :
    CompleteGridBound κ A E c q t μ realGrid (realValues (pruneValues h b m)) := by
  intro j
  by_cases hj : j.val ≤ b
  · have hg := grid_mono hj hb
    have huv : realGrid j ≤ realGrid (gridIndex b) := by
      simp only [realGrid,gridIndex_val _ hb]
      exact_mod_cast hg
    have hs := completeHingeBound_shift κ A E c q t μ hμ _ _ _ _ hm huv (hh (gridIndex b))
    have hr := completeHingeBound_min κ A E c q t μ _ _ _ (hh j) hs
    convert hr using 1
    simp only [realGrid,realValues,pruneValues,if_pos hj,gridIndex_val _ hb,
      Nat.cast_min,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hg]
    rw [← min_div_div_right scale_pos.le]
    congr 1
    ring
  · simpa only [realValues,pruneValues,if_neg hj] using hh j

end Grid
#print axioms rounded_prefix_loss
#print axioms completeGridBound_rounded_loss
#print axioms completeGridBound_pruneValues
end Erdos7No9Certificate
