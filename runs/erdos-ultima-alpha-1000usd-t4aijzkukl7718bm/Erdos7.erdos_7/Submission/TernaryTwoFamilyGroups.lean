import Submission.TernaryTwoFamilySlices
import Submission.TernaryTwoBlockCompression

/-! Actual five-adic event groups for complete arithmetic-model families. -/
namespace Erdos7TernaryTwoFamilyGroups
open scoped BigOperators
open Erdos7CompleteFamilyModel Erdos7TernaryTwoFamilySlices
set_option maxHeartbeats 3000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable
variable {κ : Type} [DecidableEq κ] {E : Fin 14 → ℕ} {e : κ → Fin 14 → ℕ}
variable (A : Fin 14 → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]
variable (X : κ → ∀ i,Finset (A i)) (ξ : Fin 5 → ∀ i,A i)

noncomputable def group (b : Family E e 2) (j : ℕ) (x : Fin 5) (y : A 1) : ℝ :=
  ∑ k∈b.labels.filter (fun k => e k 1=j+1),
    if y∈X k 1 then indicator A 1 (e k) (X k) (ξ x)/(b.multiplicity:ℝ) else 0

lemma group_nonneg (b : Family E e 2) (j : ℕ) (x : Fin 5) (y : A 1) :
    0≤group A X ξ b j x y := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact div_nonneg (indicator_nonneg A 1 (e k) (X k) (ξ x)) (Nat.cast_nonneg _)
  · rfl

lemma group_le_slice (b : Family E e 2) (j : ℕ) (x : Fin 5) (y : A 1) :
    group A X ξ b j x y≤slice A X ξ b (j+1) x := by
  unfold group Erdos7TernaryTwoFamilySlices.slice
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro k _
  split_ifs
  · rfl
  · exact div_nonneg (indicator_nonneg A 1 (e k) (X k) (ξ x)) (Nat.cast_nonneg _)

lemma second_indicator (k : κ) (x : Fin 5) (y : A 1) :
    indicator A 2 (e k) (X k) (Function.update (ξ x) 1 y)=
      if e k 1=0 ∨ y∈X k 1 then indicator A 1 (e k) (X k) (ξ x) else 0 := by
  exact indicator_step A 1 (by omega) (e k) (X k) (ξ x) y

/-- Exact count decomposition: the zero5 slice occurs once, and every
positive5 slice contributes its actual event group. -/
theorem count_decomposition (b : Family E e 2) (he : ∀ k i,e k i≤E i)
    (x : Fin 5) (y : A 1) :
    count A X b (Function.update (ξ x) 1 y)=
      slice A X ξ b 0 x+∑ j∈Finset.range (E 1),group A X ξ b j x y := by
  have hfilter : b.labels.filter (fun k => e k 1≤E 1)=b.labels :=
    Finset.filter_true_of_mem (fun k _ => he k 1)
  have hp := sum_filter_level_le b.labels (fun k => e k 1) (E 1)
    (fun k => indicator A 2 (e k) (X k) (Function.update (ξ x) 1 y))
  rw [hfilter] at hp
  unfold count
  rw [hp,add_div]
  congr 1
  · unfold Erdos7TernaryTwoFamilySlices.slice
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [second_indicator,if_pos (Or.inl (Finset.mem_filter.mp hk).2)]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    unfold group
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    have heq := (Finset.mem_filter.mp hk).2
    have hne : e k 1≠0 := by omega
    rw [second_indicator]
    simp only [hne,false_or]
    split_ifs <;> simp

/-- The actual density cap gives the required group marginal, with each
family retaining its own labels and normalized old-section weights. -/
theorem group_marginal (b : Family E e 2) (j : ℕ) (x : Fin 5)
    (ν : Fin 5 → A 1 → ℝ) (ρ : A 1 → ℝ)
    (hcap : ∀ x y,ν x y≤ρ y/5)
    (hd : ∀ k,e k 1≠0 → (∑ y,if y∈X k 1 then ρ y else 0)≤1/(5:ℝ)^(e k 1)) :
    (∑ y,ν x y*group A X ξ b j x y)≤
      (1/5)*(1/(5:ℝ)^(j+1))*slice A X ξ b (j+1) x := by
  let L := b.labels.filter (fun k => e k 1=j+1)
  have hm : (0:ℝ)≤b.multiplicity := Nat.cast_nonneg _
  have hh := Erdos7KernelFamilyCompression.event_group_marginal (ν x) ρ
    (1/5) 1 (1/(5:ℝ)^(j+1)) (by norm_num) (by norm_num)
    (fun y => by convert hcap x y using 1 <;> ring)
    (fun k : L => indicator A 1 (e k.val) (X k.val) (ξ x)/(b.multiplicity:ℝ))
    (fun k => div_nonneg (indicator_nonneg A 1 (e k.val) (X k.val) (ξ x)) hm)
    (fun k : L => fun y : A 1 => y∈X k.val 1)
    (fun k => by
      have heq := (Finset.mem_filter.mp k.property).2
      simpa only [heq] using hd k.val (by omega))
  have hgroup (y : A 1) : (∑ k : L,if y∈X k.val 1 then
      indicator A 1 (e k.val) (X k.val) (ξ x)/(b.multiplicity:ℝ) else 0)=group A X ξ b j x y := by
    exact Finset.sum_coe_sort L (fun k => if y∈X k 1 then
      indicator A 1 (e k) (X k) (ξ x)/(b.multiplicity:ℝ) else 0)
  have hslice : (∑ k : L,indicator A 1 (e k.val) (X k.val) (ξ x)/(b.multiplicity:ℝ))=
      slice A X ξ b (j+1) x := by
    rw [Finset.sum_coe_sort L (fun k => indicator A 1 (e k) (X k) (ξ x)/(b.multiplicity:ℝ))]
    exact (Finset.sum_div ..).symm
  simpa only [hgroup,hslice,one_mul] using hh

#print axioms count_decomposition
end Erdos7TernaryTwoFamilyGroups
