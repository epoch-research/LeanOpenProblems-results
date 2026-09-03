import Submission.RootFreePhaseStructure

/-! Reconstruction of a quadratic factor after a root-free coordinate
elimination. The pivot coordinate is omitted; no root choices occur. -/
namespace Erdos3RootFreeCoordinateReconstruction
open Finset Erdos3RootFreePhaseStructure Erdos3RootFreeQuadraticDilation
  Erdos3BoundedFrequencyPhaseApproximation Erdos3FiniteUniformity
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def reconstruct (j : I) (n : ℕ) (k : I → ℤ) (c v : I → ℂ) (i : I) : ℂ :=
  if i = j then c i*(∏ l ∈ univ.erase j, (v l)^(-k l)) else c i*(v i)^n

lemma solve_pivot (j : I) (n : ℕ) (k : I → ℤ) (hk : k j = n)
    (v : I → ℂ) (hv : ∀ i, ‖v i‖ = 1) :
    (v j)^n = integerPhase k v*(∏ l ∈ univ.erase j, (v l)^(-k l)) := by
  have he : (∏ l ∈ univ.erase j, (v l)^(k l))*(v j)^n = integerPhase k v := by
    have ht := prod_erase_mul (univ : Finset I) (fun l ↦ (v l)^(k l)) (mem_univ j)
    simpa only [hk,zpow_natCast,integerPhase] using ht
  have hab : (∏ l ∈ univ.erase j, (v l)^(k l))*(∏ l ∈ univ.erase j, (v l)^(-k l)) = 1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro l hl
    rw [zpow_neg,mul_inv_cancel₀]
    exact zpow_ne_zero _ (norm_ne_zero_iff.mp (by rw [hv]; norm_num))
  calc
    _ = (v j)^n*((∏ l ∈ univ.erase j, (v l)^(k l))*(∏ l ∈ univ.erase j, (v l)^(-k l))) := by rw [hab,mul_one]
    _ = ((∏ l ∈ univ.erase j, (v l)^(k l))*(v j)^n)*(∏ l ∈ univ.erase j, (v l)^(-k l)) := by ring
    _ = _ := by rw [he]

lemma reconstruct_norm (j : I) (n : ℕ) (k : I → ℤ) (c v : I → ℂ)
    (hc : ∀ i, ‖c i‖ = 1) (hv : ∀ i, ‖v i‖ = 1) (i : I) :
    ‖reconstruct j n k c v i‖ = 1 := by
  by_cases hi : i = j <;>
    simp only [reconstruct,hi,if_true,if_false,norm_mul,norm_prod,norm_zpow,norm_pow,
      hc,hv,one_zpow,one_pow,prod_const_one,one_mul]

/-- Reconstruction ignores the pivot input coordinate entirely. -/
lemma reconstruct_congr (j : I) (n : ℕ) (k : I → ℤ) (c v w : I → ℂ)
    (hvw : ∀ i, i ≠ j → v i = w i) : reconstruct j n k c v = reconstruct j n k c w := by
  funext i
  by_cases hi : i = j
  · simp only [reconstruct,if_pos hi]
    congr 1
    apply prod_congr rfl
    intro l hl
    rw [hvw l (mem_erase.mp hl).1]
  · simp only [reconstruct,if_neg hi,hvw i hi]

/-- The error in the eliminated coordinate is exactly the error in the
integer phase relation. All other coordinates are reconstructed exactly. -/
theorem reconstruct_error (j : I) (n : ℕ) (k : I → ℤ) (hk : k j = n)
    (c v : I → ℂ) (hc : ∀ i, ‖c i‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (herr : ‖integerPhase k v-1‖ ≤ δ) (i : I) :
    ‖c i*(v i)^n-reconstruct j n k c v i‖ ≤ δ := by
  by_cases hi : i = j
  · subst i
    simp only [reconstruct,ite_true]
    have he : c j*(v j)^n-c j*(∏ l ∈ univ.erase j, (v l)^(-k l)) =
        c j*(integerPhase k v-1)*(∏ l ∈ univ.erase j, (v l)^(-k l)) := by
      rw [solve_pivot j n k hk v hv]
      ring
    rw [he,norm_mul,norm_mul,hc,one_mul]
    have hn : ‖∏ l ∈ univ.erase j, (v l)^(-k l)‖ = 1 := by
      simp only [norm_prod,norm_zpow,hv,one_zpow,prod_const_one]
    simpa only [hn,mul_one] using herr
  · simpa only [reconstruct,if_neg hi,sub_self,norm_zero] using hδ

noncomputable def fillPivot (j : I) (v : {i : I // i ≠ j} → ℂ) (i : I) : ℂ :=
  if h : i = j then 1 else v ⟨i,h⟩

noncomputable def reducedReconstruct (j : I) (n : ℕ) (k : I → ℤ) (c : I → ℂ)
    (v : {i : I // i ≠ j} → ℂ) : I → ℂ := reconstruct j n k c (fillPivot j v)

lemma reconstruct_restrict (j : I) (n : ℕ) (k : I → ℤ) (c v : I → ℂ) :
    reducedReconstruct j n k c (fun i ↦ v i) = reconstruct j n k c v := by
  apply reconstruct_congr
  intro i hi
  simp only [fillPivot,dif_neg hi]

lemma reducedReconstruct_norm (j : I) (n : ℕ) (k : I → ℤ) (c : I → ℂ)
    (v : {i : I // i ≠ j} → ℂ) (hc : ∀ i, ‖c i‖ = 1) (hv : ∀ i, ‖v i‖ = 1) (i : I) :
    ‖reducedReconstruct j n k c v i‖ = 1 := by
  apply reconstruct_norm j n k c (fillPivot j v) hc
  intro l
  by_cases hl : l = j
  · simp only [fillPivot,dif_pos hl,norm_one]
  · simp only [fillPivot,dif_neg hl,hv]

#print axioms reconstruct_error
#print axioms reconstruct_restrict
end Erdos3RootFreeCoordinateReconstruction
