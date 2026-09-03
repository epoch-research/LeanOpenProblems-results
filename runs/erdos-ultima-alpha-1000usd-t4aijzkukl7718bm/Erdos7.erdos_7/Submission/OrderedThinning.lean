import Submission.CappedBudgetStep

/-! Nonnegative antitone thinning preserves the ordered positive coefficient
structure, while scaling an actual kernel gives exactly the thinned mass.
These are auxiliary kernel facts, not a solution of the covering problem. -/
namespace Erdos7OrderedThinning
open scoped BigOperators
open Erdos7CappedRetentionRows Erdos7FiniteRetentionKernel
set_option autoImplicit false
set_option maxHeartbeats 1500000

lemma coefficient_scale (τ h : ℝ) (hτ : 0 ≤ τ) (q : ℕ → ℝ) (R : ℕ)
    (d : Option (Fin R)) :
    coefficient (τ*h) (fun j => τ*q j) R d = τ*coefficient h q R d := by
  cases d <;> simp only [coefficient,← mul_min_of_nonneg _ _ hτ] <;> ring

lemma antitone_mul_nonneg {α : Type*} [Preorder α] (f g : α → ℝ)
    (hf : Antitone f) (hg : Antitone g) (hf0 : ∀ x,0 ≤ f x) (hg0 : ∀ x,0 ≤ g x) :
    Antitone (fun x => f x*g x) := by
  intro x y hxy
  exact mul_le_mul (hf hxy) (hg hxy) (hg0 y) (hf0 x)

/-- Unlike arbitrary adaptive caps, this family preserves a common ordering
for every coefficient, so independently indexed future tests remain valid. -/
theorem thinned_coefficients_antitone {α : Type*} [Preorder α]
    (h τ : α → ℝ) (hh : Antitone h) (hτ : Antitone τ) (hτ0 : ∀ x,0 ≤ τ x)
    (q : ℕ → ℝ) (R : ℕ) (hq : ∀ j,q (j+1) ≤ q j) (d : Option (Fin R)) :
    Antitone (fun x => coefficient (τ x*h x) (fun j => τ x*q j) R d) := by
  simp_rw [coefficient_scale _ _ (hτ0 _) q R d]
  apply antitone_mul_nonneg τ _ hτ ((coefficient_monotone q R hq d).comp_antitone hh) hτ0
  intro x
  exact coefficient_nonneg (h x) q R hq d

noncomputable def factor (θ h : ℝ) : ℝ := 1-θ+θ*h

lemma factor_bounds (θ h : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    0 ≤ factor θ h ∧ factor θ h ≤ 1 := by
  unfold factor
  constructor
  · nlinarith [mul_nonneg hθ hh]
  · nlinarith [mul_nonneg hθ (sub_nonneg.mpr hh1)]

lemma factor_antitone {α : Type*} [Preorder α] (θ : ℝ) (hθ : 0 ≤ θ)
    (h : α → ℝ) (hh : Antitone h) : Antitone (fun x => factor θ (h x)) := by
  intro x y hxy
  unfold factor
  have hm := mul_le_mul_of_nonneg_left (hh hxy) hθ
  dsimp only
  linarith

lemma factor_retention (θ h : ℝ) : factor θ h*h = (1-θ)*h+θ*h^2 := by
  unfold factor
  ring

/-- Scaling a single already chosen kernel preserves avoidance and gives
both the adaptive density cap and exact new mass, simultaneously for all tests. -/
theorem thin_kernel {Ω A : Type*} [Fintype A]
    (μ : Ω → ℝ) (ρ : A → ℝ) (ν : Ω → A → ℝ) (h τ : Ω → ℝ) (c : ℝ)
    (hτ : ∀ x,0 ≤ τ x) (hν : ∀ x y,0 ≤ ν x y)
    (hcap : ∀ x y,ν x y ≤ c*μ x*ρ y)
    (hmass : ∀ x,(∑ y,ν x y) = μ x*h x)
    (bad : Ω → A → Prop) (hbad : ∀ x y,bad x y → ν x y = 0) :
    let ν' := fun x y => τ x*ν x y
    (∀ x y,0 ≤ ν' x y) ∧
      (∀ x y,ν' x y ≤ (τ x*c)*μ x*ρ y) ∧
      (∀ x,(∑ y,ν' x y) = μ x*(τ x*h x)) ∧
      (∀ x y,bad x y → ν' x y = 0) := by
  dsimp only
  refine ⟨fun x y => mul_nonneg (hτ x) (hν x y),?_,?_,?_⟩
  · intro x y
    have hh := mul_le_mul_of_nonneg_left (hcap x y) (hτ x)
    convert hh using 1 <;> ring
  · intro x
    rw [← Finset.mul_sum,hmass x]
    ring
  · intro x y hb
    rw [hbad x y hb,mul_zero]

/-- Local future cost under thinning is an affine interpolation with the
unit cost. This explains why thinning can help only in conjunction with a
nonconstant continuation and a nontrivial source budget. -/
lemma thinned_cost (τ h future : ℝ) :
    1-τ*h+τ*future = (1-τ)+τ*(1-h+future) := by ring

#print axioms coefficient_scale
#print axioms thinned_coefficients_antitone
#print axioms factor_bounds
#print axioms factor_antitone
#print axioms thin_kernel
end Erdos7OrderedThinning
