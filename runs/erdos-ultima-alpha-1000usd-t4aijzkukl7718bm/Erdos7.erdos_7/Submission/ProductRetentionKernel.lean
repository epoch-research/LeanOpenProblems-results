import Submission.FiniteRetentionKernel
import Submission.RootPruning

/-! Product-block retention with separate row, column and joint density caps.
This is a genuine finite kernel construction, not a full covering sieve. -/
namespace Erdos7ProductRetentionKernel
open scoped BigOperators
open Erdos7RootPruning Erdos7FiniteRetentionKernel
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B]

/-- First restrict to the allowed row and column sets, remove the mixed bad
set, then scale/thin. The density scale need not be a product of marginal caps. -/
theorem exists_kernel (ρ : A → ℝ) (σ : B → ℝ)
    (hρ : ∀ x, 0 ≤ ρ x) (hσ : ∀ y, 0 ≤ σ y)
    (P : A → Prop) (Q : B → Prop) (D : A → B → Prop)
    (U V d ca cb cab s h : ℝ)
    (hU : (∑ x, keep ρ P x) = U) (hV : (∑ y, keep σ Q y) = V)
    (hD : (∑ x, ∑ y, if D x y then ρ x*σ y else 0) ≤ d)
    (hs : 0 ≤ s) (hsa : s*V ≤ ca) (hsb : s*U ≤ cb) (hsab : s ≤ cab)
    (hh : 0 ≤ h) (hhbound : h ≤ max 0 (s*(U*V-d))) :
    ∃ ν : A → B → ℝ,
      (∀ x y, 0 ≤ ν x y) ∧
      (∀ x y, ν x y ≤ cab*ρ x*σ y) ∧
      (∀ x, (∑ y, ν x y) ≤ ca*ρ x) ∧
      (∀ y, (∑ x, ν x y) ≤ cb*σ y) ∧
      (∀ x y, (¬ P x ∨ ¬ Q y ∨ D x y) → ν x y = 0) ∧
      (∑ x, ∑ y, ν x y) = h := by
  let α := keep ρ P
  let β := keep σ Q
  have hα (x : A) : 0 ≤ α x := keep_nonneg ρ hρ P x
  have hβ (y : B) : 0 ≤ β y := keep_nonneg σ hσ Q y
  have hαρ (x : A) : α x ≤ ρ x := keep_le ρ hρ P x
  have hβσ (y : B) : β y ≤ σ y := keep_le σ hσ Q y
  have hUV : 0 ≤ U ∧ 0 ≤ V := by
    rw [← hU, ← hV]
    exact ⟨Finset.sum_nonneg (fun x _ => hα x), Finset.sum_nonneg (fun y _ => hβ y)⟩
  let w : A × B → ℝ := fun z => if D z.1 z.2 then 0 else s*α z.1*β z.2
  have hw (z : A × B) : 0 ≤ w z := by
    dsimp only [w]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg hs (hα z.1)) (hβ z.2)
  have hwp (x : A) (y : B) : w (x,y) ≤ s*α x*β y := by
    dsimp only [w]
    split_ifs
    · exact mul_nonneg (mul_nonneg hs (hα x)) (hβ y)
    · exact le_rfl
  have hcell (x : A) (y : B) : w (x,y) ≤ cab*ρ x*σ y := by
    have hp : α x*β y ≤ ρ x*σ y := mul_le_mul (hαρ x) (hβσ y) (hβ y) (hρ x)
    have hh₁ := mul_le_mul_of_nonneg_left hp hs
    have hh₂ := mul_le_mul_of_nonneg_right hsab (mul_nonneg (hρ x) (hσ y))
    nlinarith [hwp x y]
  have hrow (x : A) : (∑ y, w (x,y)) ≤ ca*ρ x := by
    calc
      _ ≤ ∑ y, s*α x*β y := Finset.sum_le_sum (fun y _ => hwp x y)
      _ = (s*V)*α x := by rw [← Finset.mul_sum, show (∑ y, β y) = V from hV]; ring
      _ ≤ (s*V)*ρ x := mul_le_mul_of_nonneg_left (hαρ x) (mul_nonneg hs hUV.2)
      _ ≤ _ := mul_le_mul_of_nonneg_right hsa (hρ x)
  have hcol (y : B) : (∑ x, w (x,y)) ≤ cb*σ y := by
    calc
      _ ≤ ∑ x, s*α x*β y := Finset.sum_le_sum (fun x _ => hwp x y)
      _ = (s*U)*β y := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, show (∑ x, α x) = U from hU]
      _ ≤ (s*U)*σ y := mul_le_mul_of_nonneg_left (hβσ y) (mul_nonneg hs hUV.1)
      _ ≤ _ := mul_le_mul_of_nonneg_right hsb (hσ y)
  have hzero (x : A) (y : B) (hz : ¬ P x ∨ ¬ Q y ∨ D x y) : w (x,y) = 0 := by
    rcases hz with hp | hq | hd
    · simp [w, α, keep, hp]
    · simp [w, β, keep, hq]
    · simp [w, hd]
  have hbad : (∑ x, ∑ y, if D x y then α x*β y else 0) ≤ d := by
    apply LE.le.trans _ hD
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y _
    split_ifs
    · exact mul_le_mul (hαρ x) (hβσ y) (hβ y) (hρ x)
    · exact le_rfl
  have hmass : (∑ z, w z) = s*(U*V-(∑ x, ∑ y, if D x y then α x*β y else 0)) := by
    have hp (x : A) (y : B) : w (x,y) = s*(α x*β y-(if D x y then α x*β y else 0)) := by
      dsimp only [w]
      split_ifs <;> ring
    rw [Fintype.sum_prod_type]
    simp_rw [hp, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [show (∑ y, β y) = V from hV, ← Finset.sum_mul,
      show (∑ x, α x) = U from hU]
  have hlower : s*(U*V-d) ≤ ∑ z, w z := by
    rw [hmass]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hbad _) hs
  have hhavailable : h ≤ ∑ z, w z := hhbound.trans
    (max_le (Finset.sum_nonneg (fun z _ => hw z)) hlower)
  obtain ⟨ν,hν,hνmass⟩ := exists_thinning (fun _ : Unit => w) (fun _ => h)
    (fun _ z => hw z) (fun _ => hh) (fun _ => hhavailable)
  refine ⟨fun x y => ν () (x,y), (fun x y => (hν () (x,y)).1), ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact (hν () (x,y)).2.trans (hcell x y)
  · intro x
    exact (Finset.sum_le_sum (fun y _ => (hν () (x,y)).2)).trans (hrow x)
  · intro y
    exact (Finset.sum_le_sum (fun x _ => (hν () (x,y)).2)).trans (hcol y)
  · intro x y hz
    exact le_antisymm (by simpa only [hzero x y hz] using (hν () (x,y)).2) (hν () (x,y)).1
  · simpa only [Fintype.sum_prod_type] using hνmass ()

/-- This scale saturates whichever of the joint, row or column bounds is
most restrictive. Scaling is chosen after mixed deletion, not before it. -/
lemma density_caps (U V ca cb cab : ℝ) (hU : 0 < U) (hV : 0 < V)
    (ha : 0 ≤ ca) (hb : 0 ≤ cb) (hab : 0 ≤ cab) :
    let s := min cab (min (ca/V) (cb/U))
    0 ≤ s ∧ s ≤ cab ∧ s*V ≤ ca ∧ s*U ≤ cb := by
  dsimp only
  refine ⟨le_min hab (le_min (div_nonneg ha hV.le) (div_nonneg hb hU.le)),
    min_le_left _ _, ?_, ?_⟩
  · exact (le_div_iff₀ hV).mp ((min_le_right _ _).trans (min_le_left _ _))
  · exact (le_div_iff₀ hU).mp ((min_le_right _ _).trans (min_le_right _ _))

#print axioms exists_kernel
#print axioms density_caps
end Erdos7ProductRetentionKernel
