import Submission.AdaptiveCappedRows
import Submission.KernelFamilyCompression

/-!
Pointwise variable-cap kernels and one-family compression. These are local
auxiliary theorems, not a complete adaptive arithmetic tower or a settlement.
-/
namespace Erdos7AdaptiveCappedKernel
open scoped BigOperators
open Erdos7FiniteRetentionKernel Erdos7KernelFamilyCompression Erdos7CappedRetentionRows
set_option maxHeartbeats 1500000

/-- A different nonnegative cap may be used at each old-coordinate point. -/
theorem exists_variable_cap_kernel {Ω A : Type*} [Fintype A]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ρ : A → ℝ)
    (hρ : ∀ y, 0 ≤ ρ y) (hρmass : (∑ y, ρ y)=1)
    (bad : Ω → A → Prop) [∀ x y, Decidable (bad x y)]
    (h c : Ω → ℝ) (hc : ∀ x, 0 ≤ c x) (hh : ∀ x, 0 ≤ h x)
    (hfeasible : ∀ x, h x ≤ c x*(1-∑ y, if bad x y then ρ y else 0)) :
    ∃ ν : Ω → A → ℝ,
      (∀ x y, 0 ≤ ν x y) ∧
      (∀ x y, ν x y ≤ c x*μ x*ρ y) ∧
      (∀ x y, bad x y → ν x y=0) ∧
      (∀ x, (∑ y, ν x y)=μ x*h x) := by
  classical
  have hex (x : Ω) : ∃ v : A → ℝ,
      (∀ y, 0 ≤ v y) ∧ (∀ y, v y ≤ c x*μ x*ρ y) ∧
      (∀ y, bad x y → v y=0) ∧ (∑ y, v y)=μ x*h x := by
    obtain ⟨v, hv, hcap, hzero, hmass⟩ := exists_retention_kernel
      (fun _ : Unit => μ x) (fun _ => hμ x) ρ hρ hρmass
      (fun _ y => bad x y) (fun _ => h x) (c x) (hc x) (fun _ => hh x)
      (fun _ => hfeasible x)
    exact ⟨v (), hv (), hcap (), hzero (), hmass ()⟩
  choose ν hν hcap hzero hmass using hex
  exact ⟨ν, hν, hcap, hzero, hmass⟩

/-- The existing actual-family compression is pointwise in the old coordinate,
so a variable cap does not identify any distinct old cumulative families. -/
theorem variable_cap_compression {Ω A I : Type*}
    [Fintype Ω] [Fintype A] [Fintype I]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ν : Ω → A → ℝ)
    (hν : ∀ x y, 0 ≤ ν x y) (h : Ω → ℝ) (hh : ∀ x, 0 ≤ h x)
    (hmass : ∀ x, (∑ y, ν x y)=μ x*h x)
    (ρ : A → ℝ) (c : Ω → ℝ) (hc : ∀ x, 0 ≤ c x)
    (hcap : ∀ x y, ν x y ≤ c x*μ x*ρ y)
    (R : ℕ) (r : ℕ → ℝ) (hrR : r R=0)
    (w : ℕ → I → Ω → ℝ) (hw : ∀ j<R, ∀ i x, 0 ≤ w j i x)
    (hit : ℕ → I → A → Prop) [∀ j i y, Decidable (hit j i y)]
    (hdensity : ∀ j<R, ∀ i, (∑ y, if hit j i y then ρ y else 0) ≤ r j)
    (Z : Option (Fin R) → Ω → ℝ) (Y : Ω → A → ℝ)
    (hcount : ∀ x y, Y x y = Z none x +
      ∑ j ∈ Finset.range R, ∑ i, if hit j i y then w j i x else 0)
    (hprefix : ∀ (j : Fin R) x,
      Z none x + ∑ g ∈ Finset.range (j.val+1), ∑ i, w g i x =
        multiplier (some j)*Z (some j) x)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ x, ∑ y, ν x y*φ (Y x y)) ≤
      ∑ x, μ x*(∑ d, coefficient (h x) (fun j => c x*r j) R d *
        φ (multiplier d*Z d x)) := by
  classical
  apply Finset.sum_le_sum
  intro x _
  have hx := normalized_family_compression
    (fun _ : Unit => μ x) (fun _ => hμ x) (fun _ y => ν x y)
    (fun _ y => hν x y) (fun _ => h x) (fun _ => hh x)
    (fun _ => hmass x) ρ (c x) (hc x) (fun _ y => hcap x y)
    R r hrR (fun j i _ => w j i x) (fun j hj i _ => hw j hj i x)
    hit hdensity (fun d _ => Z d x) (fun _ y => Y x y)
    (fun _ y => hcount x y) (fun j _ => hprefix j x) φ hφ hmφ
  simpa using hx

#print axioms exists_variable_cap_kernel
#print axioms variable_cap_compression
end Erdos7AdaptiveCappedKernel
