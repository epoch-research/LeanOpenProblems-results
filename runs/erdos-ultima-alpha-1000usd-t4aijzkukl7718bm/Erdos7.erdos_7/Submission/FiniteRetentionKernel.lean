import Submission.BackwardFamilyBudget
import Submission.CappedRetentionRows

/-! Actual real-valued finite retention kernels and pushforward identities.
These do not identify the count functions of different covering families. -/
namespace Erdos7FiniteRetentionKernel
open scoped BigOperators
open Erdos7CappedRetentionRows Erdos7BackwardFamilyBudget
set_option maxHeartbeats 1500000

theorem exists_thinning {Ω A : Type*} [Fintype A]
    (w : Ω → A → ℝ) (target : Ω → ℝ)
    (hw : ∀ x y, 0 ≤ w x y) (ht0 : ∀ x, 0 ≤ target x)
    (ht : ∀ x, target x ≤ ∑ y, w x y) :
    ∃ ν : Ω → A → ℝ,
      (∀ x y, 0 ≤ ν x y ∧ ν x y ≤ w x y) ∧
      (∀ x, (∑ y, ν x y) = target x) := by
  let total (x : Ω) : ℝ := ∑ y, w x y
  have htotal (x : Ω) : 0 ≤ total x := Finset.sum_nonneg (fun y _ => hw x y)
  refine ⟨fun x y => (target x / total x)*w x y, ?_, ?_⟩
  · intro x y
    constructor
    · exact mul_nonneg (div_nonneg (ht0 x) (htotal x)) (hw x y)
    · by_cases hz : total x=0
      · simp only [hz, div_zero, zero_mul]
        exact hw x y
      · have hp : 0 < total x := lt_of_le_of_ne (htotal x) (Ne.symm hz)
        have hh : target x / total x ≤ 1 := (div_le_one hp).mpr (ht x)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (hw x y)
  · intro x
    rw [← Finset.mul_sum]
    change target x / total x * total x = target x
    by_cases hz : total x=0
    · have hz' : target x=0 := le_antisymm (by simpa only [← hz] using ht x) (ht0 x)
      simp [hz']
    · exact div_mul_cancel₀ _ hz

/-- Retain precisely the desired old-coordinate mass, avoid the actual bad
set, and respect the pointwise density cap against an arbitrary probability
law on the new coordinate. -/
theorem exists_retention_kernel {Ω A : Type*} [Fintype A]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (ρ : A → ℝ)
    (hρ : ∀ y, 0 ≤ ρ y) (hρmass : (∑ y, ρ y)=1)
    (bad : Ω → A → Prop) [∀ x y, Decidable (bad x y)] (h : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hh : ∀ x, 0 ≤ h x)
    (hfeasible : ∀ x, h x ≤ c*(1-∑ y, if bad x y then ρ y else 0)) :
    ∃ ν : Ω → A → ℝ,
      (∀ x y, 0 ≤ ν x y) ∧
      (∀ x y, ν x y ≤ c*μ x*ρ y) ∧
      (∀ x y, bad x y → ν x y=0) ∧
      (∀ x, (∑ y, ν x y)=μ x*h x) := by
  classical
  let w (x : Ω) (y : A) : ℝ := if bad x y then 0 else c*μ x*ρ y
  have hw (x : Ω) (y : A) : 0 ≤ w x y := by
    dsimp [w]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg hc (hμ x)) (hρ y)
  have hs (x : Ω) : (∑ y, w x y)=c*μ x*(1-∑ y, if bad x y then ρ y else 0) := by
    calc
      _ = ∑ y, c*μ x*(ρ y-(if bad x y then ρ y else 0)) := by
        apply Finset.sum_congr rfl
        intro y _
        dsimp [w]
        split_ifs <;> ring
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_sub_distrib, hρmass]
  have hav (x : Ω) : μ x*h x ≤ ∑ y, w x y := by
    rw [hs]
    have hm := mul_le_mul_of_nonneg_left (hfeasible x) (hμ x)
    nlinarith
  obtain ⟨ν, hν, hmass⟩ := exists_thinning w (fun x => μ x*h x) hw
    (fun x => mul_nonneg (hμ x) (hh x)) hav
  refine ⟨ν, (fun x y => (hν x y).1), ?_, ?_, hmass⟩
  · intro x y
    apply (hν x y).2.trans
    dsimp [w]
    split_ifs
    · exact mul_nonneg (mul_nonneg hc (hμ x)) (hρ y)
    · exact le_rfl
  · intro x y hbad
    apply le_antisymm _ (hν x y).1
    simpa [w, hbad] using (hν x y).2

noncomputable def push {Ω Ξ : Type*} [Fintype Ω]
    (f : Ω → Ξ) (ν : Ω → ℝ) (z : Ξ) : ℝ := by
  classical
  exact ∑ x, if f x=z then ν x else 0

lemma push_integral {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (f : Ω → Ξ) (ν : Ω → ℝ) (φ : Ξ → ℝ) :
    (∑ z, push f ν z*φ z) = ∑ x, ν x*φ (f x) := by
  classical
  simp only [push, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul, eq_comm]

lemma push_mass {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (f : Ω → Ξ) (ν : Ω → ℝ) : (∑ z, push f ν z) = ∑ x, ν x := by
  simpa only [mul_one] using push_integral f ν (fun _ => 1)

lemma push_nonneg {Ω Ξ : Type*} [Fintype Ω]
    (f : Ω → Ξ) (ν : Ω → ℝ) (hν : ∀ x, 0 ≤ ν x) (z : Ξ) :
    0 ≤ push f ν z := by
  classical
  unfold push
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact hν x
  · exact le_rfl

/-- A budget pulls back along the actual pushforward map without any change
of family labels or diagonal tests. -/
lemma budget_of_push {Ω Ξ α : Type} [Fintype Ω] [Fintype Ξ]
    (f : Ω → Ξ) (ν : Ω → ℝ) (X : α → Ξ → ℝ) (F : ℝ → ℝ) (lo hi : ℝ)
    (hb : HasBudget (push f ν) X F lo hi) :
    HasBudget ν (fun a x => X a (f x)) F lo hi := by
  obtain ⟨ι, inst, b, pick, φ, hφ, hdiag, hbound⟩ := hb
  letI : Fintype ι := inst
  refine ⟨ι, inst, b, pick, φ, hφ, hdiag, ?_⟩
  simpa only [push_mass, push_integral] using hbound

#print axioms exists_retention_kernel
#print axioms budget_of_push
end Erdos7FiniteRetentionKernel
