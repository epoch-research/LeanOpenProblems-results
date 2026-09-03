import FormalConjecturesUtil
import Submission.ThetaHeavyShadow

/-! A bounded colouring of the light graph gives a linear incidence bound.
The existence of a bounded colouring is an additional hypothesis. -/
open Finset
open scoped Classical
namespace Erdos713ThetaLightColoring
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
variable {A B I : Type*}
set_option maxHeartbeats 2000000

lemma color_fiber_bound [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (χ : B → I)
    (hχ : ∀ x y, x ≠ y → χ x = χ y → 3 ≤ codegree R x y) (i : I) :
    (∑ a : A, ((row R a).filter (fun x => χ x = i)).card) ≤ 3*Fintype.card A := by
  let Q : A → {x : B // χ x = i} → Prop := fun a x => R a x.val
  have hQ : ¬ HasTheta Q := by
    rintro ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩
    exact hf ⟨a,fun j => (b j).val,ha,Subtype.val_injective.comp hb,
      h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hH : Heavy Q := by
    intro x y hxy
    have hne : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    exact hχ x.val y.val hne (x.property.trans y.property.symm)
  have hh := incidences_le_three_rows hQ hH
  have hc (a : A) : (row Q a).card = ((row R a).filter (fun x => χ x = i)).card := by
    have he := Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun x : B => χ x = i) (R a))
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype,row,filter_filter,Q,and_comm] using he
  simpa only [hc] using hh

lemma incidences_le [Fintype A] [Fintype B] [Fintype I] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (χ : B → I)
    (hχ : ∀ x y, x ≠ y → χ x = χ y → 3 ≤ codegree R x y) :
    (∑ a : A, (row R a).card) ≤ 3*Fintype.card I*Fintype.card A := by
  have hrow (a : A) : (row R a).card =
      ∑ i : I, ((row R a).filter (fun x => χ x = i)).card :=
    card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
  calc
    _ = ∑ a : A, ∑ i : I, ((row R a).filter (fun x => χ x = i)).card := by simp only [hrow]
    _ = ∑ i : I, ∑ a : A, ((row R a).filter (fun x => χ x = i)).card := sum_comm
    _ ≤ ∑ _i : I, 3*Fintype.card A := sum_le_sum (fun i _ => color_fiber_bound hf χ hχ i)
    _ = _ := by simp; ring

#print axioms color_fiber_bound
#print axioms incidences_le
end Erdos713ThetaLightColoring
