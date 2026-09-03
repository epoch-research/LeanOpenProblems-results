import Submission.Forest93ConcreteEvents

/-! Avoiding at most84 normalized mixed boxes in the eight-prime profile. -/
namespace Erdos7Forest93Concrete
open scoped BigOperators
open Erdos7Forest93Certificate Erdos7Forest93Shapes Erdos7ForestRestricted
open Erdos7ForestUnion Erdos7RootOverlapCompensation Erdos7ForestProduct
open Erdos7Forest93Events
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option autoImplicit false

def selectedBox (S : Finset Index) (r : Index → Space) (i : Index) : Space → Prop :=
  fun x => i ∈ S ∧ residueBox i (r i) x
lemma selectedBox_mass (b : Fin 9) (S : Finset Index) (r : Index → Space) (i : Index) :
    mass (measure b) (selectedBox S r i) = mass (measure b) (residueBox i (r i))*selection S i := by
  unfold selectedBox
  by_cases hi : i ∈ S
  · simp [selectedBox,hi,selection_mem S i hi]
  · simp [selectedBox,hi,selection_not_mem S i hi,mass,bit]

lemma selected_union_lt_one (b : Fin 9) (hb : b.val%3 ≠ 0) (S : Finset Index)
    (hcard : S.card ≤ 84) (hmixed : ∀ i ∈ S,mixed i)
    (r : Index → Space) (hr : ∀ i ∈ S,good i (r i)) :
    mass (measure b) (fun x => ∃ i,selectedBox S r i x) < 1 := by
  apply union_mass_lt_one (measure b) (measure_nonneg b) (selectedBox S r) S hcard
  · intro i
    rw [selectedBox_mass]
    by_cases hi : i ∈ S
    · rw [selection_mem S i hi,mul_one,mul_one]
      exact residueBox_mass_le b hb i (hmixed i hi) (r i)
    · simp only [selection_not_mem S i hi,mul_zero,le_refl]
  · intro e he
    by_cases h₁ : e.1 ∈ S
    · by_cases h₂ : e.2 ∈ S
      · unfold selectedBox
        simp only [h₁,h₂,true_and]
        exact le_of_eq (residueBox_independent b hb e.1 e.2 (r e.1) (r e.2)
          (ordinary_disjoint ⟨e,he⟩)).symm
      · rw [selectedBox_mass b S r e.2,selection_not_mem S e.2 h₂,mul_zero,mul_zero]
        exact mass_nonneg _ (measure_nonneg b) _
    · rw [selectedBox_mass b S r e.1,selection_not_mem S e.1 h₁,mul_zero,zero_mul]
      exact mass_nonneg _ (measure_nonneg b) _
  · intro h₁ h₂
    refine ⟨rootProbability b (r 192 0),rootProbability b (r 160 0),?_,?_,?_,?_,?_⟩
    · exact rootProbability_cases b _ hb ((hr 192 h₁).1 (by rw [pivot_exponents.1]; decide))
    · exact rootProbability_cases b _ hb ((hr 160 h₂).1 (by rw [pivot_exponents.2]; decide))
    · unfold selectedBox
      simp only [h₁,true_and]
      exact pivot192_mass b hb _ (hr 192 h₁)
    · unfold selectedBox
      simp only [h₂,true_and]
      exact pivot160_mass b hb _ (hr 160 h₂)
    · simp only [selectedBox,h₁,h₂,true_and]
      exact pivot_intersection_lower b hb _ _ (hr 192 h₁) (hr 160 h₂)

lemma measure_zero_outside (b : Fin 9) (x : Space) (hx : ¬∀ j,x j ∈ allowed b j) : measure b x = 0 := by
  obtain ⟨j,hj⟩ := not_forall.mp hx
  unfold measure productWeight
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [law,restricted,bit,hj]

theorem exists_uncovered (b : Fin 9) (hb : b.val%3 ≠ 0) (S : Finset Index)
    (hcard : S.card ≤ 84) (hmixed : ∀ i ∈ S,mixed i)
    (r : Index → Space) (hr : ∀ i ∈ S,good i (r i)) :
    ∃ x : Space,(∀ j,x j ∈ allowed b j) ∧ ∀ i ∈ S,¬residueBox i (r i) x := by
  classical
  by_contra h
  push_neg at h
  have he : mass (measure b) (fun x => ∃ i,selectedBox S r i x) =
      mass (measure b) (fun _ => True) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ∀ j,x j ∈ allowed b j
    · obtain ⟨i,hi,hix⟩ := h x hx
      have hh : ∃ i,selectedBox S r i x := ⟨i,hi,hix⟩
      simp only [bit,if_pos hh,if_true]
    · rw [measure_zero_outside b x hx,zero_mul,zero_mul]
  have hh := selected_union_lt_one b hb S hcard hmixed r hr
  rw [he,measure_full b hb] at hh
  exact lt_irrefl _ hh

#print axioms exists_uncovered
end Erdos7Forest93Concrete
