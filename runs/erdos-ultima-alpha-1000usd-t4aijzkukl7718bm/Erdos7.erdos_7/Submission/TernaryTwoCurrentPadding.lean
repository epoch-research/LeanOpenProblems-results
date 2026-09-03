import Submission.TernaryTwoSharedPrefix
import Submission.FiniteRetentionKernel

/-! Positive full-slice padding is valid at the initial retention step. It
only overestimates the actual bad-fiber mass; no completed cover is assumed. -/
namespace Erdos7TernaryTwoCurrentPadding
open scoped BigOperators
open Erdos7TernaryTwoSharedPrefix
set_option maxHeartbeats 2000000
variable {J : Type*} [Fintype J]

noncomputable def paddedWeight (w : J → ℝ) : Option J → ℝ :=
  Option.elim' (1-∑ j,w j) w

def paddedChoice (c : Fin 10) (a : J → Fin 10) : Option J → Fin 10 :=
  Option.elim' c a

lemma paddedWeight_nonneg (w : J → ℝ) (hw : ∀ j,0≤w j) (hs : (∑ j,w j)≤1) :
    ∀ j,0≤paddedWeight w j := by
  intro j; cases j with
  | none => exact sub_nonneg.mpr hs
  | some j => exact hw j

lemma paddedWeight_mass (w : J → ℝ) : (∑ j,paddedWeight w j)=1 := by
  simp [paddedWeight,Fintype.sum_option]

noncomputable def paddedCount (w : J → ℝ) (c : Fin 10) (a : J → Fin 10) (x : Fin 5) : ℝ :=
  ∑ j,paddedWeight w j*(count (paddedChoice c a j) x : ℝ)

lemma paddedCount_expansion (w : J → ℝ) (c : Fin 10) (a : J → Fin 10) (x : Fin 5) :
    paddedCount w c a x = (1-∑ j,w j)*(count c x : ℝ)+∑ j,w j*(count (a j) x : ℝ) := by
  simp [paddedCount,paddedWeight,paddedChoice,Fintype.sum_option]

lemma paddedCount_dominates (w : J → ℝ) (hs : (∑ j,w j)≤1)
    (c : Fin 10) (a : J → Fin 10) (x : Fin 5) :
    (∑ j,w j*(count (a j) x : ℝ)) ≤ paddedCount w c a x := by
  rw [paddedCount_expansion]
  have hh := mul_nonneg (sub_nonneg.mpr hs) (Nat.cast_nonneg (α := ℝ) (count c x))
  linarith

lemma paddedCount_bounds (w : J → ℝ) (hw : ∀ j,0≤w j) (hs : (∑ j,w j)≤1)
    (c : Fin 10) (a : J → Fin 10) (x : Fin 5) :
    1≤paddedCount w c a x ∧ paddedCount w c a x≤3 := by
  have hh := paddedWeight_nonneg w hw hs
  constructor
  · calc
      1 = ∑ j,paddedWeight w j*1 := by simp only [mul_one,paddedWeight_mass]
      _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
        (by exact_mod_cast (data.1 (paddedChoice c a j) x).1) (hh j))
  · calc
      _ ≤ ∑ j,paddedWeight w j*3 := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
        (by exact_mod_cast (data.1 (paddedChoice c a j) x).2) (hh j))
      _ = 3 := by rw [← Finset.sum_mul,paddedWeight_mass,one_mul]

lemma retention_affine (w : J → ℝ) (c : Fin 10) (a : J → Fin 10) (x : Fin 5) :
    1-paddedCount w c a x/4 =
      ∑ j,paddedWeight w j*(1-(count (paddedChoice c a j) x : ℝ)/4) := by
  simp only [mul_sub,mul_one,← mul_div_assoc,Finset.sum_sub_distrib,← Finset.sum_div,
    paddedWeight_mass]
  rfl

/-- The exact retained law can use a convex mixture of full current slices,
even when the actual finite geometric weights have total strictly below one.
An artificial slice only reduces retention, so it cannot invalidate avoidance. -/
theorem exists_padded_kernel {A : Type*} [Fintype A]
    (w : J → ℝ) (hw : ∀ j,0≤w j) (hs : (∑ j,w j)≤1)
    (c : Fin 10) (a : J → Fin 10)
    (ρ : A → ℝ) (hρ : ∀ y,0≤ρ y) (hρmass : (∑ y,ρ y)=1)
    (bad : Fin 5 → A → Prop) [∀ x y,Decidable (bad x y)]
    (hbad : ∀ x,(∑ y,if bad x y then ρ y else 0) ≤
      (∑ j,w j*(count (a j) x : ℝ))/4) :
    ∃ ν : Fin 5 → A → ℝ,
      (∀ x y,0≤ν x y) ∧ (∀ x y,ν x y≤ρ y/5) ∧
      (∀ x y,bad x y → ν x y=0) ∧
      (∀ x,(∑ y,ν x y)=(1-paddedCount w c a x/4)/5) := by
  obtain ⟨ν,hν,hcap,hzero,hmass⟩ := Erdos7FiniteRetentionKernel.exists_retention_kernel
    (fun _ : Fin 5 => (1:ℝ)/5) (fun _ => by norm_num) ρ hρ hρmass bad
    (fun x => 1-paddedCount w c a x/4) 1 (by norm_num)
    (fun x => by have hh := (paddedCount_bounds w hw hs c a x).2; linarith)
    (fun x => by
      have h₁ := hbad x
      have h₂ := paddedCount_dominates w hs c a x
      nlinarith)
  refine ⟨ν,hν,?_,hzero,?_⟩
  · intro x y
    convert hcap x y using 1 <;> ring
  · intro x
    convert hmass x using 1 <;> ring

#print axioms exists_padded_kernel
#print axioms retention_affine
end Erdos7TernaryTwoCurrentPadding
