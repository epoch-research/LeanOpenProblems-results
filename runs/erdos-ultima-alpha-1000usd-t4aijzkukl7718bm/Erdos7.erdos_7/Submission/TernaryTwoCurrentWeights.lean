import Submission.TernaryTwoCurrentSlices
import Submission.TernaryTwoBlockCompression

/-! Push the padded current mixture to the ten common integer corners. -/
namespace Erdos7TernaryTwoCurrentWeights
open scoped BigOperators
open Erdos7CompleteFamilyModel Erdos7TernaryTwoCoherentMixture
open Erdos7TernaryTwoCurrentPadding Erdos7TernaryTwoCurrentSlices
open Erdos7TernaryTwoSliceDomination
set_option maxHeartbeats 3000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

lemma pushWeight_eval {I Z : Type*} [Fintype I] [Fintype Z]
    (w : I → ℝ) (f : I → Z) (g : Z → ℝ) :
    (∑ z,pushWeight w f z*g z)=∑ i,w i*g (f i) := by
  classical
  unfold pushWeight
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

noncomputable def currentWeight (R : ℕ) (c : Fin R → Fin 10) : Fin 10 → ℝ :=
  pushWeight (paddedWeight (weight R)) (paddedChoice 0 c)

lemma currentWeight_nonneg (R : ℕ) (c : Fin R → Fin 10) : ∀ a,0≤currentWeight R c a :=
  pushWeight_nonneg _ _ (paddedWeight_nonneg _ (weight_nonneg R) (weight_mass R))

lemma currentWeight_mass (R : ℕ) (c : Fin R → Fin 10) : (∑ a,currentWeight R c a)=1 := by
  rw [currentWeight,pushWeight_mass,paddedWeight_mass]

lemma currentWeight_retention (R : ℕ) (c : Fin R → Fin 10) (x : Fin 5) :
    Erdos7TernaryTwoBlockCompression.retention (currentWeight R c) x=
      1-paddedCount (weight R) 0 c x/4 := by
  unfold Erdos7TernaryTwoBlockCompression.retention currentWeight
  rw [pushWeight_eval]
  exact (retention_affine (weight R) 0 c x).symm

variable (E : Fin 14 → ℕ)
variable (A : Fin 14 → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]
variable (X : Pattern E → ∀ i,Finset (A i)) (ξ : Fin 5 → ∀ i,A i)

/-- A genuine cap1 kernel for the actual current bad set, expressed directly
in the common current-corner probability weights. -/
theorem exists_kernel (hE : E 0=2)
    (hbranch : ∀ k,exponent E k 0=1 → ∃ q : Fin 2,∀ x,
      indicator A 1 (exponent E k) (X k) (ξ x)≤(if branch x=q then (1:ℝ) else 0))
    (hpoint : ∀ k,exponent E k 0=2 → ∃ y : Fin 5,∀ x,
      indicator A 1 (exponent E k) (X k) (ξ x)≤(if x=y then (1:ℝ) else 0))
    (ρ : A 1 → ℝ) (hρ : ∀ y,0≤ρ y) (hρmass : (∑ y,ρ y)=1)
    (hd : ∀ k,exponent E k 1≠0 →
      (∑ y,if y∈X k 1 then ρ y else 0)≤1/(5:ℝ)^(exponent E k 1)) :
    ∃ (w : Fin 10 → ℝ) (ν : Fin 5 → A 1 → ℝ),
      (∀ c,0≤w c) ∧ (∑ c,w c)=1 ∧
      (∀ x y,0≤ν x y) ∧ (∀ x y,ν x y≤ρ y/5) ∧
      (∀ x y,currentBad A E X 1 (by omega) (ξ x) y → ν x y=0) ∧
      (∀ x,(∑ y,ν x y)=Erdos7TernaryTwoBlockCompression.retention w x/5) := by
  obtain ⟨c,ν,hν,hcap,hzero,hmass⟩ := exists_current_kernel E A X ξ hE hbranch hpoint ρ hρ hρmass hd
  refine ⟨currentWeight (E 1) c,ν,currentWeight_nonneg _ _,currentWeight_mass _ _,hν,hcap,hzero,?_⟩
  intro x
  rw [currentWeight_retention]
  exact hmass x

#print axioms exists_kernel
end Erdos7TernaryTwoCurrentWeights
