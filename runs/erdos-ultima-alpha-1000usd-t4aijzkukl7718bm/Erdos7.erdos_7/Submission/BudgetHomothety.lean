import Submission.BackwardFamilyBudget

/-! Positive rescaling about the constant budget one. Changing only this
scale does not change the existence of a family-budget certificate. -/
namespace Erdos7BudgetHomothety
open scoped BigOperators
open Erdos7BackwardFamilyBudget
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {Ω α : Type} [Fintype Ω]

def scale (ε : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ := 1+ε*(F t-1)

lemma scale_comp (ε : ℝ) (hε : ε ≠ 0) (F : ℝ → ℝ) :
    scale (1/ε) (scale ε F) = F := by
  funext t
  simp only [scale]
  field_simp
  ring

lemma scale_lt_one (ε : ℝ) (hε : 0 < ε) (F : ℝ → ℝ) (t : ℝ) :
    scale ε F t < 1 ↔ F t < 1 := by
  dsimp only [scale]
  constructor <;> intro h
  · nlinarith
  · nlinarith

/-- Every witness transforms by multiplying its convex tests by ε and
replacing its constant b with 1+ε*(b-1). No sign assumption on μ is needed. -/
theorem budget_scale (μ : Ω → ℝ) (X : α → Ω → ℝ) (F : ℝ → ℝ)
    (lo hi ε : ℝ) (hε : 0 ≤ ε) (hb : HasBudget μ X F lo hi) :
    HasBudget μ X (scale ε F) lo hi := by
  classical
  obtain ⟨ι, inst, b, pick, φ, hφ, hdiag, hbudget⟩ := hb
  letI : Fintype ι := inst
  refine ⟨ι, inst, 1+ε*(b-1), pick, (fun i t => ε*φ i t), ?_, ?_, ?_⟩
  · intro i
    constructor
    · simpa only [smul_eq_mul] using (hφ i).1.smul hε
    · intro s t hst
      exact mul_le_mul_of_nonneg_left ((hφ i).2 hst) hε
  · intro t ht
    rw [← Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left (hdiag t ht) hε
    dsimp only [scale]
    linarith
  · have he : (∑ x, μ x*(1+ε*(b-1)+∑ i, ε*φ i (X (pick i) x))) =
        (∑ x, μ x)+ε*((∑ x, μ x*(b+∑ i, φ i (X (pick i) x)))-(∑ x, μ x)) := by
      have hp (x : Ω) : μ x*(1+ε*(b-1)+∑ i, ε*φ i (X (pick i) x)) =
          μ x+ε*(μ x*(b+∑ i, φ i (X (pick i) x))-μ x) := by
        rw [← Finset.mul_sum]
        ring
      simp_rw [hp]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hbudget hε]

/-- Positive homotheties preserve budget existence in BOTH directions. -/
theorem budget_scale_iff (μ : Ω → ℝ) (X : α → Ω → ℝ) (F : ℝ → ℝ)
    (lo hi ε : ℝ) (hε : 0 < ε) :
    HasBudget μ X (scale ε F) lo hi ↔ HasBudget μ X F lo hi := by
  constructor
  · intro hb
    have hh := budget_scale μ X (scale ε F) lo hi (1/ε) (by positivity) hb
    rwa [scale_comp ε hε.ne'] at hh
  · exact budget_scale μ X F lo hi ε hε.le

lemma ternary_affine_eq (ε : ℝ) :
    (fun t : ℝ => 1+ε*(t-2)) = scale ε (fun t => t-1) := by
  funext t
  simp only [scale]
  ring

theorem ternary_affine_budget_iff (μ : Ω → ℝ) (X : α → Ω → ℝ)
    (lo hi ε : ℝ) (hε : 0 < ε) :
    HasBudget μ X (fun t => 1+ε*(t-2)) lo hi ↔
      HasBudget μ X (fun t => t-1) lo hi := by
  rw [ternary_affine_eq]
  exact budget_scale_iff μ X (fun t => t-1) lo hi ε hε

#print axioms budget_scale_iff
#print axioms ternary_affine_budget_iff
end Erdos7BudgetHomothety
