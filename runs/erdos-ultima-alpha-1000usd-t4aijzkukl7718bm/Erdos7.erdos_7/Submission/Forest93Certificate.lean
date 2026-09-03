import Submission.Forest93Check0
import Submission.Forest93Check1
import Submission.Forest93Check2
import Submission.Forest93Check4
import Submission.Forest93Check5
import Submission.Forest93Check6
import Submission.Forest93Check7
import Submission.Forest93Check8

/-! Rational transfer from separately kernel-checked integer forest data.
No arithmetic covering-system theorem is asserted here. -/
namespace Erdos7Forest93Certificate
open scoped BigOperators
open Erdos7ForestCapacity
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option Elab.async false
lemma denominator_pos : (0:ℚ) < denominator := by norm_num [denominator]
lemma denominator_ne : (denominator:ℚ) ≠ 0 := ne_of_gt denominator_pos
lemma weight_nonneg (i : Index) : 0 ≤ weight i := div_nonneg (Nat.cast_nonneg _) denominator_pos.le
lemma coefficient_nonneg (e : Index × Index) : 0 ≤ coefficient e := by
  unfold coefficient
  split_ifs
  · norm_num
  · exact mul_nonneg (weight_nonneg _) (weight_nonneg _)

lemma edges_parent : ∀ e ∈ edges,parent e.1 = some e.2 := fun e he => edges_parent_checked ⟨e,he⟩

lemma coefficient_eq (e : Index × Index) (he : e ∈ edges) :
    coefficient e = (coefficientNum e:ℚ)/denominator := by
  by_cases hf : e = forced
  · subst e
    norm_num [coefficient,coefficientNum,denominator]
  · have hd := coefficient_divides ⟨e,he⟩ hf
    simp only [coefficient,coefficientNum,if_neg hf,weight]
    rw [Nat.cast_div hd denominator_ne,Nat.cast_mul]
    ring

lemma degree_eq (i : Index) : neighbor ordinary weight i = (degreeNum i:ℚ)/denominator := by
  classical
  unfold neighbor degreeNum
  rw [Nat.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp [weight,Nat.cast_add,add_div]

lemma incident_eq (i : Index) : incident edges coefficient i = (incidentNum i:ℚ)/denominator := by
  classical
  unfold incident incidentNum
  rw [Nat.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp [coefficient_eq e he,Nat.cast_add,add_div]

lemma degree_bound (i : Index) : neighbor ordinary weight i ≤ 1 := by
  rw [degree_eq]
  apply (div_le_one₀ denominator_pos).mpr
  exact_mod_cast degreeNum_bound i
lemma pivot_degree : neighbor ordinary weight 192 ≤ 1/2 ∧
    neighbor ordinary weight 160 ≤ 1/4 := by
  obtain ⟨h₁,h₂⟩ := pivot_degreeNum
  have h₁' : (2:ℚ)*degreeNum 192 ≤ denominator := by exact_mod_cast h₁
  have h₂' : (4:ℚ)*degreeNum 160 ≤ denominator := by exact_mod_cast h₂
  constructor
  · rw [degree_eq]
    apply (div_le_iff₀ denominator_pos).mpr
    linarith
  · rw [degree_eq]
    apply (div_le_iff₀ denominator_pos).mpr
    linarith

lemma hinge_bound (i : Index) : max (weight i-incident edges coefficient i-1/864) 0 ≤
    ((weightNum i-incidentNum i-105600:ℕ):ℚ)/denominator := by
  rw [incident_eq]
  apply max_le _ (div_nonneg (Nat.cast_nonneg _) denominator_pos.le)
  have hn : weightNum i ≤ (weightNum i-incidentNum i-105600)+incidentNum i+105600 := by omega
  have hq : (weightNum i:ℚ) ≤ ((weightNum i-incidentNum i-105600:ℕ):ℚ)+incidentNum i+105600 := by exact_mod_cast hn
  unfold weight
  norm_num only [denominator,Nat.cast_ofNat] at *
  linarith

lemma value_bound : thresholdValue ≤ (certificateTotal:ℚ)/denominator := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hinge_bound i)
  have hc : (∑ e ∈ edges,coefficient e) = ((∑ e ∈ edges,coefficientNum e:ℕ):ℚ)/denominator := by
    rw [Nat.cast_sum,Finset.sum_div]
    exact Finset.sum_congr rfl (fun e he => coefficient_eq e he)
  rw [← Finset.sum_div] at hs
  unfold thresholdValue certificateTotal
  rw [hc]
  simp only [Nat.cast_add,Nat.cast_sum,Nat.cast_mul,Nat.cast_ofNat]
  norm_num only [denominator,Nat.cast_ofNat] at *
  linarith

lemma value_lt_one : thresholdValue < 1 := by
  apply value_bound.trans_lt
  rw [total_checked]
  norm_num [denominator]

theorem selection_certificate (x : Index → ℚ) (hx : ∀ i,0 ≤ x i ∧ x i ≤ 1)
    (hcard : (∑ i,x i) ≤ 84) :
    (∑ i,weight i*x i)-(∑ e ∈ edges,coefficient e*x e.1*x e.2) < 1 := by
  have hh := forest_threshold_bound edges weight x coefficient coefficient 84 (1/864)
    hx hcard (by norm_num) (fun e he => ⟨coefficient_nonneg e,le_rfl⟩)
  exact hh.trans_lt value_lt_one

#print axioms total_checked
#print axioms selection_certificate
end Erdos7Forest93Certificate
