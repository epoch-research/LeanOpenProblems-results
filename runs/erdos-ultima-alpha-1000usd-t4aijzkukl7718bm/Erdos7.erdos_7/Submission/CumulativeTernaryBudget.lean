import Submission.CumulativeHingeDefect
import Submission.CumulativeTernaryExample

/-! Finite geometric hinge bound for one specified fourteen-cell current profile.
This is not a universal current-profile or arithmetic covering-system theorem. -/
namespace Erdos7CumulativeTernaryBudget
open scoped BigOperators
open Erdos7CumulativeHingeDefect Erdos7CumulativeTernaryExample
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def μ (x : Fin 14) : ℝ := if keep x then 1/14 else 0

lemma μ_nonneg (x : Fin 14) : 0 ≤ μ x := by unfold μ; split_ifs <;> norm_num

lemma count_pos (a : Fin 140) (x : Fin 14) : 1 ≤ count a x := by
  unfold count
  omega

lemma weighted_sum (f : Fin 14 → ℕ) :
    (∑ x,μ x*(f x : ℝ)) = ((∑ x,if keep x then f x else 0 : ℕ) : ℝ)/14 := by
  rw [Nat.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : keep x
  · simp only [μ,if_pos hx]
    ring
  · simp [μ,hx]

lemma mean_eq (a : Fin 140) :
    (∑ x,μ x*(count a x : ℝ)) = (meanNum a : ℝ)/14 := weighted_sum _

lemma mean_bound (a : Fin 140) : (∑ x,μ x*(count a x : ℝ)) ≤ 24/14 := by
  rw [mean_eq]
  have hh : meanNum a ≤ 24 := by
    have hh := (single_bounds a).1
    split_ifs at hh <;> omega
  have hc : (meanNum a : ℝ) ≤ 24 := by exact_mod_cast hh
  linarith

lemma μ_mass : (∑ x,μ x)=13/14 := by
  have hn : (∑ x : Fin 14,if keep x then 1 else 0 : ℕ)=13 := by decide +kernel
  have hh := weighted_sum (fun _ => 1)
  simpa only [Nat.cast_one,mul_one,hn,Nat.cast_ofNat] using hh

lemma both_eq (a : ℕ → Fin 140) :
    bothMass μ (fun j x => count (a j) x) = (bothNum (a 0) (a 1) : ℝ)/14 := by
  unfold bothMass bothNum
  rw [Nat.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : keep x
  · simp only [μ,if_pos hx]
    by_cases hh : count (a 0) x=1 ∧ count (a 1) x=1 <;> simp [hh,hx]
  · simp [μ,hx]

lemma prefix_two (a : ℕ → Fin 140) :
    prefixCost μ (fun j x => count (a j) x) 2 =
      ((meanNum (a 0) : ℝ)+(meanNum (a 1) : ℝ)-39+(bothNum (a 0) (a 1) : ℝ))/14 := by
  unfold prefixCost
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  simp_rw [two_hinge_identity _ _ (count_pos (a 0) _) (count_pos (a 1) _)]
  simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [mean_eq,mean_eq,← Finset.sum_mul,μ_mass]
  have hb := both_eq a
  unfold bothMass at hb
  rw [hb]
  ring

/-- The finite capped-mixture cost, with the separately weighted first slice
and the same sequence of slices in every cumulative term. -/
noncomputable def finiteCost (a : ℕ → Fin 140) (R : ℕ) : ℝ :=
  (firstNum (a 0) : ℝ)/280+
    prefixCost μ (fun j x => count (a j) x) 1/5+
    drift (fun j => prefixCost μ (fun i x => count (a i) x) (j+1)) R

/-- This bound includes every positive finite geometric depth, not only a
truncated numerical prefix. It applies only to the specified current profile. -/
theorem finiteCost_bound (a : ℕ → Fin 140) (R : ℕ) (hR : 1 ≤ R) :
    finiteCost a R ≤ 61/200 := by
  have hh := prefix_geometric_bound μ μ_nonneg (fun j x => count (a j) x)
    (fun j x => count_pos (a j) x) (24/14)
    (fun j _ => mean_bound (a j)) R hR
  rw [both_eq] at hh
  have he : (firstNum (a 0) : ℝ)/280+
      prefixCost μ (fun j x => count (a j) x) 2/5+(24/14)/20-
        ((bothNum (a 0) (a 1) : ℝ)/14)/25 =
      ((pairScore (a 0) (a 1) : ℝ)-660)/1400 := by
    rw [prefix_two]
    simp only [pairScore,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have hp : (pairScore (a 0) (a 1) : ℝ) ≤ 1087 := by
    exact_mod_cast pair_bound (a 0) (a 1)
  unfold finiteCost
  linarith

#print axioms prefix_two
#print axioms finiteCost_bound
end Erdos7CumulativeTernaryBudget
