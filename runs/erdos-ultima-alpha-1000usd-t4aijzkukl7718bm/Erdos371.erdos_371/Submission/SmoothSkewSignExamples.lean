import Submission.SmoothCutoffSkew

/-! Finite signed checks for the smooth-cutoff kernel. They rule out a
uniform finite sign, not either asymptotic conclusion in the conjecture. -/
namespace Erdos371
open Finset

lemma smoothCutoffSkew_eq_count_difference (B C N : ℕ) :
    smoothCutoffSkew B C N =
      (((range N).filter (fun n => Nat.maxPrimeFac (n+1) ≤ B ∧ Nat.maxPrimeFac (n+2) ≤ C)).card : ℝ)-
      (((range N).filter (fun n => Nat.maxPrimeFac (n+1) ≤ C ∧ Nat.maxPrimeFac (n+2) ≤ B)).card : ℝ) := by
  have he (B C a b : ℕ) : smoothIndicator B a*smoothIndicator C b =
      if Nat.maxPrimeFac a ≤ B ∧ Nat.maxPrimeFac b ≤ C then (1 : ℝ) else 0 := by
    unfold smoothIndicator
    split_ifs <;> simp_all
  simp only [smoothCutoffSkew,he,sum_sub_distrib,sum_boole]

lemma smoothCutoffSkew_five_seven_six : smoothCutoffSkew 5 7 6 = 1 := by
  have h₁ : ((range 6).filter (fun n => Nat.maxPrimeFac (n+1) ≤ 5 ∧ Nat.maxPrimeFac (n+2) ≤ 7)).card = 6 := by
    decide +kernel
  have h₂ : ((range 6).filter (fun n => Nat.maxPrimeFac (n+1) ≤ 7 ∧ Nat.maxPrimeFac (n+2) ≤ 5)).card = 5 := by
    decide +kernel
  rw [smoothCutoffSkew_eq_count_difference,h₁,h₂]
  norm_num

lemma smoothCutoffSkew_five_seven_fourteen : smoothCutoffSkew 5 7 14 = -1 := by
  have h₁ : ((range 14).filter (fun n => Nat.maxPrimeFac (n+1) ≤ 5 ∧ Nat.maxPrimeFac (n+2) ≤ 7)).card = 8 := by
    decide +kernel
  have h₂ : ((range 14).filter (fun n => Nat.maxPrimeFac (n+1) ≤ 7 ∧ Nat.maxPrimeFac (n+2) ≤ 5)).card = 9 := by
    decide +kernel
  rw [smoothCutoffSkew_eq_count_difference,h₁,h₂]
  norm_num

#print axioms smoothCutoffSkew_five_seven_six
#print axioms smoothCutoffSkew_five_seven_fourteen
end Erdos371
