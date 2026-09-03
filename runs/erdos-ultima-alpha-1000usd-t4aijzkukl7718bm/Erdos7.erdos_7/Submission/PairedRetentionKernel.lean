import Submission.FiniteRetentionKernel

/-! A genuine three-live-state retention kernel for two candidate points.
The common density cap applies to the SUM of the three states. This is a
finite kernel construction, not an unrestricted covering-system budget. -/
namespace Erdos7PairedRetentionKernel
open scoped BigOperators
open Erdos7FiniteRetentionKernel
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

/-- Discard a fiber only when both candidates are bad. The three live-state
kernels use a single thinning and therefore share one pointwise density cap. -/
theorem exists_paired_kernel {Ω A : Type*} [Fintype A]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ρ : A → ℝ)
    (hρ : ∀ y, 0 ≤ ρ y) (hm : (∑ y, ρ y) = 1)
    (P Q : Ω → A → Prop) (h : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hh : ∀ x, 0 ≤ h x)
    (hfeasible : ∀ x, h x ≤ c * (1 - ∑ y, if P x y ∧ Q x y then ρ y else 0)) :
    ∃ L R B : Ω → A → ℝ,
      (∀ x y, 0 ≤ L x y ∧ 0 ≤ R x y ∧ 0 ≤ B x y) ∧
      (∀ x y, L x y + R x y + B x y ≤ c * μ x * ρ y) ∧
      (∀ x y, P x y → L x y = 0 ∧ B x y = 0) ∧
      (∀ x y, Q x y → R x y = 0 ∧ B x y = 0) ∧
      (∀ x y, ¬ Q x y → L x y = 0) ∧
      (∀ x y, ¬ P x y → R x y = 0) ∧
      (∀ x, (∑ y, (L x y + R x y + B x y)) = μ x * h x) := by
  obtain ⟨ν, hν, hcap, hbad, hmass⟩ :=
    exists_retention_kernel μ hμ ρ hρ hm (fun x y => P x y ∧ Q x y)
      h c hc hh hfeasible
  let L (x : Ω) (y : A) := if Q x y then ν x y else 0
  let R (x : Ω) (y : A) := if P x y then ν x y else 0
  let B (x : Ω) (y : A) := if P x y ∨ Q x y then 0 else ν x y
  have he (x : Ω) (y : A) : L x y + R x y + B x y = ν x y := by
    by_cases hp : P x y <;> by_cases hq : Q x y
    · simp [L, R, B, hp, hq, hbad x y ⟨hp, hq⟩]
    · simp [L, R, B, hp, hq]
    · simp [L, R, B, hp, hq]
    · simp [L, R, B, hp, hq]
  refine ⟨L, R, B, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    dsimp [L, R, B]
    exact ⟨ite_nonneg (hν x y) (le_refl _),
      ite_nonneg (hν x y) (le_refl _), ite_nonneg (le_refl _) (hν x y)⟩
  · intro x y
    rw [he]
    exact hcap x y
  · intro x y hp
    constructor
    · by_cases hq : Q x y
      · simp [L, hq, hbad x y ⟨hp, hq⟩]
      · simp [L, hq]
    · simp [B, hp]
  · intro x y hq
    constructor
    · by_cases hp : P x y
      · simp [R, hp, hbad x y ⟨hp, hq⟩]
      · simp [R, hp]
    · simp [B, hq]
  · intro x y hq
    simp [L, hq]
  · intro x y hp
    simp [R, hp]
  · intro x
    simpa only [he] using hmass x

noncomputable def eventMass {A : Type*} [Fintype A]
    (ρ : A → ℝ) (P : A → Prop) : ℝ := ∑ y, if P y then ρ y else 0

lemma eventMass_nonneg {A : Type*} [Fintype A]
    (ρ : A → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (P : A → Prop) :
    0 ≤ eventMass ρ P :=
  Finset.sum_nonneg (fun y _ => ite_nonneg (hρ y) (le_refl _))

/-- The overlap is constrained by Frechet bounds, not by a product of the
marginal expectations. No independence is asserted. -/
theorem overlap_bounds {A : Type*} [Fintype A]
    (ρ : A → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hm : (∑ y, ρ y) = 1)
    (P Q : A → Prop) :
    max 0 (eventMass ρ P + eventMass ρ Q - 1) ≤ eventMass ρ (fun y => P y ∧ Q y) ∧
    eventMass ρ (fun y => P y ∧ Q y) ≤ min (eventMass ρ P) (eventMass ρ Q) := by
  have hleft : eventMass ρ (fun y => P y ∧ Q y) ≤ eventMass ρ P := by
    apply Finset.sum_le_sum
    intro y _
    by_cases hp : P y <;> by_cases hq : Q y <;> simp [hp, hq, hρ y]
  have hright : eventMass ρ (fun y => P y ∧ Q y) ≤ eventMass ρ Q := by
    apply Finset.sum_le_sum
    intro y _
    by_cases hp : P y <;> by_cases hq : Q y <;> simp [hp, hq, hρ y]
  have hlower : eventMass ρ P + eventMass ρ Q - eventMass ρ (fun y => P y ∧ Q y) ≤ 1 := by
    rw [eventMass, eventMass, eventMass, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← hm]
    apply Finset.sum_le_sum
    intro y _
    by_cases hp : P y <;> by_cases hq : Q y <;> simp [hp, hq, hρ y]
  exact ⟨max_le (eventMass_nonneg ρ hρ _) (by linarith), le_min hleft hright⟩

noncomputable def pairCost (P Q : Prop) (left right both : ℝ) : ℝ :=
  if P ∧ Q then 1 else if P then right else if Q then left else both

lemma pairCost_identity (P Q : Prop) (left right both : ℝ) :
    pairCost P Q left right both = both +
      (right - both) * (if P then 1 else 0) +
      (left - both) * (if Q then 1 else 0) +
      (1 + both - left - right) * (if P ∧ Q then 1 else 0) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [pairCost, hp, hq] <;> ring

/-- Exact single-step cost before thinning. The joint bad mass is essential;
separate marginal loss estimates cannot replace it by a product. -/
theorem expected_pairCost {A : Type*} [Fintype A]
    (ρ : A → ℝ) (hm : (∑ y, ρ y) = 1) (P Q : A → Prop)
    (left right both : ℝ) :
    (∑ y, ρ y * pairCost (P y) (Q y) left right both) =
      both + (right - both) * eventMass ρ P + (left - both) * eventMass ρ Q +
        (1 + both - left - right) * eventMass ρ (fun y => P y ∧ Q y) := by
  have he (y : A) : ρ y * pairCost (P y) (Q y) left right both =
      ρ y * both + (right - both) * (if P y then ρ y else 0) +
        (left - both) * (if Q y then ρ y else 0) +
          (1 + both - left - right) * (if P y ∧ Q y then ρ y else 0) := by
    by_cases hp : P y <;> by_cases hq : Q y <;> simp [pairCost, hp, hq] <;> ring
  simp_rw [he, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hm, one_mul]
  simp only [eventMass, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  by_cases hp : P y ∧ Q y <;> simp [hp]

/-- A valid bound using only the two marginal bad masses. The sign of the
joint coefficient determines which Frechet endpoint must be used. -/
theorem expected_pairCost_le {A : Type*} [Fintype A]
    (ρ : A → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hm : (∑ y, ρ y) = 1)
    (P Q : A → Prop) (left right both : ℝ) :
    (∑ y, ρ y * pairCost (P y) (Q y) left right both) ≤
      both + (right - both) * eventMass ρ P + (left - both) * eventMass ρ Q +
        max 0 (1 + both - left - right) * min (eventMass ρ P) (eventMass ρ Q) +
        min 0 (1 + both - left - right) * max 0 (eventMass ρ P + eventMass ρ Q - 1) := by
  rw [expected_pairCost ρ hm]
  obtain ⟨hl, hu⟩ := overlap_bounds ρ hρ hm P Q
  by_cases hz : 0 ≤ 1 + both - left - right
  · rw [max_eq_right hz, min_eq_left hz, zero_mul, add_zero]
    linarith [mul_le_mul_of_nonneg_left hu hz]
  · have hz' : 1 + both - left - right ≤ 0 := le_of_not_ge hz
    rw [max_eq_left hz', min_eq_right hz', zero_mul, add_zero]
    linarith [mul_le_mul_of_nonpos_left hl hz']

/-- Even for a two-point probability space the overlap can exceed the product
of the two marginal masses. Independence cannot be inferred from their values. -/
theorem marginal_product_not_an_overlap_bound :
    eventMass (fun _ : Bool => (1 / 2 : ℝ)) (fun y => y = true) *
        eventMass (fun _ : Bool => (1 / 2 : ℝ)) (fun y => y = true) <
      eventMass (fun _ : Bool => (1 / 2 : ℝ)) (fun y => y = true ∧ y = true) := by
  norm_num [eventMass, Fintype.sum_bool]


/-- Two distinct coarse ternary residues cannot lie in the same class of
any modulus divisible by three. -/
lemma ternary_class_thin (m x y a : ℤ) (hm : 3 ∣ m) (hxy : ¬ 3 ∣ x-y) :
    ¬ (m ∣ x-a ∧ m ∣ y-a) := by
  rintro ⟨hx, hy⟩
  apply hxy
  have h := hm.trans (dvd_sub hx hy)
  convert h using 1 <;> ring

#print axioms exists_paired_kernel
#print axioms overlap_bounds
#print axioms expected_pairCost
#print axioms ternary_class_thin
end Erdos7PairedRetentionKernel
