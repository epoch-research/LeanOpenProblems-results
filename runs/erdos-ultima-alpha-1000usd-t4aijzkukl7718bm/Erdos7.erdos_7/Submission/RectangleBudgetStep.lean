import Submission.RectangleFamilies
import Submission.CappedBudgetStep

/-! An exact-retention budget step on concrete complete exponent rectangles. -/
namespace Erdos7CompleteFamilyModel
open scoped BigOperators
open Erdos7BackwardFamilyBudget Erdos7CappedRetentionRows
open Erdos7FiniteRetentionKernel Erdos7KernelFamilyCompression Erdos7CappedBudgetStep
set_option maxHeartbeats 2500000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

lemma padded_mean_bounds {J : Type} [Fintype J] (w X : J → ℝ) (H : ℝ)
    (hw : ∀ j,0 ≤ w j) (hs : (∑ j,w j) ≤ 1) (hH : 1 ≤ H)
    (hX : ∀ j,1 ≤ X j ∧ X j ≤ H) :
    1 ≤ (1-∑ j,w j)+∑ j,w j*X j ∧
    (1-∑ j,w j)+∑ j,w j*X j ≤ H := by
  have hl : (∑ j,w j) ≤ ∑ j,w j*X j := by
    apply Finset.sum_le_sum
    intro j _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hX j).1 (hw j)
  have hu : (∑ j,w j*X j) ≤ (∑ j,w j)*H := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hX j).2 (hw j))
  constructor
  · linarith
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hH)]

lemma multiplier_bounds {R : ℕ} (d : Option (Fin R)) :
    1 ≤ multiplier d ∧ multiplier d ≤ (R:ℝ)+1 := by
  cases d with
  | none => simp [multiplier]
  | some j =>
    dsimp only [multiplier]
    have hj : (j.val:ℝ)+1 ≤ (R:ℝ) := by exact_mod_cast (show j.val+1 ≤ R from j.isLt)
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) j.val]

section Step
variable (A : Fin n → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)]
  [∀ i,DecidableEq (A i)]
variable (E : Fin n → ℕ) (X : Pattern E → ∀ i,Finset (A i))

noncomputable def currentCount (t : ℕ) (ht : t < n) (q : ℝ) (r : ℕ → ℝ)
    (x : ∀ i,A i) : ℝ :=
  (1-∑ a : Fin (E ⟨t,ht⟩),q*r a.val) +
    ∑ a : Fin (E ⟨t,ht⟩),q*r a.val*count A X (currentFamily E t ht a) x

lemma currentCount_bounds (t : ℕ) (ht : t < n) (q : ℝ) (hq : 0 ≤ q)
    (r : ℕ → ℝ) (hr : ∀ j < E ⟨t,ht⟩,0 ≤ r j)
    (hs : (∑ a : Fin (E ⟨t,ht⟩),q*r a.val) ≤ 1) (x : ∀ i,A i) :
    currentCount A E X t ht q r x ∈ Set.Icc (1:ℝ) (capacity E t) := by
  apply padded_mean_bounds (fun a : Fin (E ⟨t,ht⟩) => q*r a.val)
    (fun a => count A X (currentFamily E t ht a) x) (capacity E t)
    (fun a => mul_nonneg hq (hr a.val a.isLt)) hs
  · exact_mod_cast capacity_pos E t
  · intro a
    exact ⟨count_lower A X _ x,count_upper A X (exponent_bound E) _ (Nat.le_of_lt ht) x⟩

lemma currentBad_le_count (t : ℕ) (ht : t < n) (q : ℝ) (hq : 0 < q)
    (r : ℕ → ℝ) (hs : (∑ a : Fin (E ⟨t,ht⟩),q*r a.val) ≤ 1)
    (ρ : A ⟨t,ht⟩ → ℝ) (hρ : ∀ y,0 ≤ ρ y)
    (hd : ∀ k : Pattern E, exponent E k ⟨t,ht⟩ ≠ 0 →
      (∑ y,if y ∈ X k ⟨t,ht⟩ then ρ y else 0) ≤ r (exponent E k ⟨t,ht⟩-1))
    (x : ∀ i,A i) :
    (∑ y,if currentBad A E X t ht x y then ρ y else 0) ≤ currentCount A E X t ht q r x/q := by
  apply (currentBad_density A E X t ht x ρ hρ r hd).trans
  apply (le_div_iff₀ hq).mpr
  dsimp only [currentCount]
  have he : (∑ a : Fin (E ⟨t,ht⟩),r a.val*count A X (currentFamily E t ht a) x)*q =
      ∑ a : Fin (E ⟨t,ht⟩),q*r a.val*count A X (currentFamily E t ht a) x := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro a _; ring
  rw [he]
  linarith

/-- Concrete form of the kernel step: all family closure, count ranges and
current-layer Jensen conditions have been discharged. -/
theorem exists_rectangle_budget_step (t : ℕ) (ht : t < n)
    (μ : (∀ i,A i) → ℝ) (hμ : ∀ x,0 ≤ μ x)
    (ρ : A ⟨t,ht⟩ → ℝ) (hρ : ∀ y,0 ≤ ρ y) (hρmass : (∑ y,ρ y) = 1)
    (q c K : ℝ) (hq : 0 < q) (hc : 0 ≤ c)
    (r : ℕ → ℝ) (hr : ∀ j < E ⟨t,ht⟩,0 ≤ r j)
    (hrdec : ∀ j,r (j+1) ≤ r j) (hrE : r (E ⟨t,ht⟩) = 0)
    (hs : (∑ a : Fin (E ⟨t,ht⟩),q*r a.val) ≤ 1)
    (hd : ∀ k : Pattern E, exponent E k ⟨t,ht⟩ ≠ 0 →
      (∑ y,if y ∈ X k ⟨t,ht⟩ then ρ y else 0) ≤ r (exponent E k ⟨t,ht⟩-1))
    (U V F G : ℝ → ℝ) (hU : ConvexOn ℝ Set.univ U) (hmU : Monotone U)
    (hV : ∀ u ∈ Set.Icc (1:ℝ) (capacity E t),0 ≤ V u)
    (hF : ∀ u ∈ Set.Icc (1:ℝ) (capacity E t),U u+V u ≤ F u)
    (hdual : ∀ k ∈ Set.Icc (1:ℝ) (capacity E t),∀ u ∈ Set.Icc (1:ℝ) (capacity E t),
      1-retained q c K k + (∑ d : Option (Fin (E ⟨t,ht⟩)),
        coefficient (retained q c K k) (fun j => c*r j) (E ⟨t,ht⟩) d *
          G (multiplier d*u)) ≤ U k+V u) :
    ∃ ν : (∀ i,A i) → A ⟨t,ht⟩ → ℝ,
      (∀ x y,0 ≤ ν x y) ∧
      (∀ x y,ν x y ≤ c*μ x*ρ y) ∧
      (∀ x y,currentBad A E X t ht x y → ν x y = 0) ∧
      (∀ x,(∑ y,ν x y) = μ x*retained q c K (currentCount A E X t ht q r x)) ∧
      (HasBudget (push (fun z : (∀ i,A i) × A ⟨t,ht⟩ => Function.update z.1 ⟨t,ht⟩ z.2)
        (fun z => ν z.1 z.2)) (count A X : Family E (exponent E) (t+1) → _)
        G 1 (capacity E (t+1)) →
        HasBudget μ (count A X : Family E (exponent E) t → _) F 1 (capacity E t)) := by
  classical
  apply exists_kernel_budget_step μ hμ ρ hρ hρmass (currentBad A E X t ht)
    q c K hq hc (currentCount A E X t ht q r)
    (currentBad_le_count A E X t ht q hq r hs ρ hρ hd)
    (E ⟨t,ht⟩) (fun j => c*r j) (fun j => mul_le_mul_of_nonneg_left (hrdec j) hc)
    (count A X) (count A X) (fun z => Function.update z.1 ⟨t,ht⟩ z.2)
    (fun b => oldFamily b ht) (currentFamily E t ht)
    U V F G 1 (capacity E t) 1 (capacity E (t+1))
    (by exact_mod_cast capacity_pos E t) hU hmU hV hF
    (currentCount_bounds A E X t ht q hq.le r hr hs) ?_ ?_
    (fun a => q*r a.val) (fun a => mul_nonneg hq.le (hr a.val a.isLt)) hs ?_ ?_ hdual
  · intro b d x
    exact ⟨count_lower A X _ x,count_upper A X (exponent_bound E) _ (Nat.le_of_lt ht) x⟩
  · intro d u hu
    have hd' := multiplier_bounds d
    constructor
    · nlinarith [hu.1,hd'.1]
    · rw [capacity_succ E t ht,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      exact (mul_le_mul_of_nonneg_left hu.2 (multiplier_nonneg d)).trans
        (mul_le_mul_of_nonneg_right hd'.2 (Nat.cast_nonneg _))
  · intro x
    dsimp only [currentCount]
    simp only [mul_one,le_refl]
  · intro ν hν hcap hmass b φ hφ hmφ
    apply complete_family_compression A X (exponent_bound E) b ht μ hμ ν hν
      (fun x => retained q c K (currentCount A E X t ht q r x))
      (fun x => retained_nonneg _ _ _ _) hmass ρ c hc hcap r hr hrE ?_ φ hφ hmφ
    intro k hk j hj he
    have hd' := hd k (by rw [he]; omega)
    simpa only [he,Nat.add_sub_cancel] using hd'

end Step
#print axioms exists_rectangle_budget_step
end Erdos7CompleteFamilyModel
