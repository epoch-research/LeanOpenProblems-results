import Submission.ForestEvents

/-! Product-coordinate event masses for the compensated forest framework. -/
namespace Erdos7ForestProduct
open scoped BigOperators
open Erdos7ForestUnion
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

lemma bit_forall {ι : Type*} [Fintype ι] (P : ι → Prop) :
    bit (∀ i,P i) = ∏ i,bit (P i) := by
  classical
  by_cases h : ∀ i,P i
  · simp [bit,h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [show bit (∀ i,P i) = 0 by simp [bit,h]]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [bit,hi])).symm

section Product
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type*) [∀ i,Fintype (A i)]

noncomputable def productWeight (ρ : ∀ i,A i → ℚ) (x : ∀ i,A i) : ℚ := ∏ i,ρ i (x i)

def box (B : ∀ i,A i → Prop) (x : ∀ i,A i) : Prop := ∀ i,B i (x i)

lemma productWeight_nonneg (ρ : ∀ i,A i → ℚ) (hρ : ∀ i a,0 ≤ ρ i a) (x : ∀ i,A i) :
    0 ≤ productWeight A ρ x := Finset.prod_nonneg (fun i _ => hρ i (x i))

/-- A box has the product of its coordinate masses. -/
theorem box_mass (ρ : ∀ i,A i → ℚ) (B : ∀ i,A i → Prop) :
    mass (productWeight A ρ) (box A B) = ∏ i,mass (ρ i) (B i) := by
  classical
  unfold mass productWeight box
  simp_rw [bit_forall,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => ρ i a*bit (B i a))).symm

lemma productWeight_mass (ρ : ∀ i,A i → ℚ) (hρ : ∀ i,(∑ a,ρ i a) = 1) :
    mass (productWeight A ρ) (fun _ => True) = 1 := by
  have hh := box_mass A ρ (fun _ _ => True)
  simpa [mass,bit,box,hρ] using hh

lemma box_intersection (B C : ∀ i,A i → Prop) (x : ∀ i,A i) :
    box A B x ∧ box A C x ↔ box A (fun i a => B i a ∧ C i a) x := by
  simp only [box]
  constructor
  · rintro ⟨hB,hC⟩ i
    exact ⟨hB i,hC i⟩
  · intro h
    exact ⟨fun i => (h i).1,fun i => (h i).2⟩

/-- Disjoint coordinate supports give exact independence, even after arbitrary
independent pure-coordinate restrictions have changed the coordinate laws. -/
theorem disjoint_box_independent (ρ : ∀ i,A i → ℚ) (hρ : ∀ i,(∑ a,ρ i a) = 1)
    (B C : ∀ i,A i → Prop)
    (hdisjoint : ∀ i,(∀ a,B i a) ∨ (∀ a,C i a)) :
    mass (productWeight A ρ) (fun x => box A B x ∧ box A C x) =
      mass (productWeight A ρ) (box A B)*mass (productWeight A ρ) (box A C) := by
  classical
  have he : (fun x => box A B x ∧ box A C x) = box A (fun i a => B i a ∧ C i a) := by
    funext x
    exact propext (box_intersection A B C x)
  rw [he,box_mass,box_mass,box_mass,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rcases hdisjoint i with hb | hc
  · have hm : mass (ρ i) (B i) = 1 := by simp [mass,bit,hb,hρ i]
    rw [hm,one_mul]
    unfold mass
    apply Finset.sum_congr rfl
    intro a _
    simp [bit,hb a]
  · have hm : mass (ρ i) (C i) = 1 := by simp [mass,bit,hc,hρ i]
    rw [hm,mul_one]
    unfold mass
    apply Finset.sum_congr rfl
    intro a _
    simp [bit,hc a]
end Product

section Uniform
variable {X : Type*} [Fintype X]
noncomputable def uniform : X → ℚ := fun _ => 1/Fintype.card X
lemma uniform_nonneg (x : X) : 0 ≤ uniform x := by unfold uniform; positivity
lemma uniform_sum [Nonempty X] : (∑ x : X,uniform x) = 1 := by
  have hn : (Fintype.card X : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt (Fintype.card_pos (α := X))
  simp [uniform,hn]
lemma uniform_mass (B : Finset X) : mass uniform (fun x => x ∈ B) = (B.card:ℚ)/Fintype.card X := by
  classical
  have hb : (∑ x : X,bit (x ∈ B)) = (B.card:ℚ) := by
    letI : DecidablePred (fun x : X => x ∈ B) := fun _ => Classical.propDecidable _
    unfold bit
    rw [Finset.sum_boole]
    congr 1
    apply congrArg Finset.card
    ext x
    simp
  unfold mass uniform
  rw [← Finset.mul_sum,hb]
  ring
end Uniform

#print axioms box_mass
#print axioms disjoint_box_independent
#print axioms uniform_mass
end Erdos7ForestProduct
