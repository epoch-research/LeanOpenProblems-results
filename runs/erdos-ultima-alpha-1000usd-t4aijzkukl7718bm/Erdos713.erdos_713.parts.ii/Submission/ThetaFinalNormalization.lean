import FormalConjecturesUtil
import Submission.ThetaRigidNormalization

/-! Combining the two finite normalizations, while retaining the column cap.
No square-scale vanishing assertion is made. -/
open Finset
open scoped Classical
namespace Erdos713ThetaFinalNormalization
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaOverlap Erdos713ThetaRowTruncation
open Erdos713ThetaRowRestriction Erdos713ThetaRigidNormalization
universe u v
variable {A : Type u} {B : Type v}
set_option maxHeartbeats 2000000

lemma column_card_le_of_subrelation {C : Type*} [Finite A] [Finite C]
    {R : A → B → Prop} {Q : C → B → Prop} {f : C → A}
    (hf : Function.Injective f) (hsub : ∀ a b, Q a b → R (f a) b) (b : B) :
    Nat.card {a : C // Q a b} ≤ Nat.card {a : A // R a b} := by
  let g : {a : C // Q a b} → {a : A // R a b} := fun a => ⟨f a.val,hsub _ _ a.property⟩
  apply Nat.card_le_card_of_injective g
  intro a c h
  apply Subtype.ext
  apply hf
  exact congrArg (fun z : {a : A // R a b} => z.val) h

/-- The punctured column relation is C4-free whenever distinct original
rows share at most two columns. This is the explicit incidence statement. -/
lemma punctured_column_four_free [Fintype B] {R : A → B → Prop}
    (hR : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (u : B) (a b : {a : A // R a u}) (x y : {x : B // x ≠ u})
    (hax : R a.val x.val) (hay : R a.val y.val)
    (hbx : R b.val x.val) (hby : R b.val y.val) : a = b ∨ x = y := by
  by_cases hab : a = b
  · exact Or.inl hab
  right
  by_contra hxy
  have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  have hxy' : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have hs : ({u,x.val,y.val} : Finset B) ⊆ row R a.val ∩ row R b.val := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> simp [mem_row,a.property,b.property,hax,hay,hbx,hby]
  have hc : ({u,x.val,y.val} : Finset B).card = 3 := by
    simp [x.property.symm,y.property.symm,hxy']
  have hh := card_le_card hs
  have hb := hR a.val b.val hab'
  omega

/-- Every theta-free relation has a subrelation with the same columns,
controlled degrees and pairwise row intersections, and explicit losses.
Every maximum-column-degree cap of the original relation is preserved. -/
theorem normalize [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (r : ℕ) (hr : 2 ≤ r) :
    ∃ (C : Type u) (_ : Fintype C) (f : C → A) (Q : C → B → Prop),
      Function.Injective f ∧ Fintype.card C ≤ Fintype.card A ∧
      (∀ a b, Q a b → R (f a) b) ∧ ¬ HasTheta Q ∧
      (∀ a, r ≤ (row Q a).card ∧
        (row Q a).card^2*(2*r-3) < 12*Fintype.card B) ∧
      (∀ a b, a ≠ b → (row Q a ∩ row Q b).card ≤ 2) ∧
      (∀ b, Nat.card {a : C // Q a b} ≤ Nat.card {a : A // R a b}) ∧
      (∑ a : A, (row R a).card) ≤ (∑ a : C, (row Q a).card) +
        21*lightCount R+(84*r^2+2*r)*Fintype.card A ∧
      lightCount Q ≤ 85*(lightCount R+4*r^2*Fintype.card A) := by
  obtain ⟨C₀,hC₀,f₀,hf₀,hcard₀,hdeg₀,hfree₀,hE₀,hL₀⟩ :=
    normalize_rows hf (2*r) (by omega)
  obtain ⟨C,hC,f₁,Q,hf₁,hcard₁,hsub,hfree,hdeg,hover,hE₁,hL₁⟩ :=
    normalize_rigid hfree₀ r hr (fun a => (hdeg₀ a).1)
  let f := f₀ ∘ f₁
  have hfi : Function.Injective f := hf₀.comp hf₁
  have hsub' (a : C) (b : B) (hab : Q a b) : R (f a) b := hsub a b hab
  have hrow (a : C) : (row Q a).card ≤ (row R (f a)).card := by
    apply card_le_card
    intro b hb
    exact (mem_row _ _ _).mpr (hsub' a b ((mem_row _ _ _).mp hb))
  refine ⟨C,hC,f,Q,hfi,hcard₁.trans hcard₀,hsub',hfree,?_,hover,?_,?_,?_⟩
  · intro a
    refine ⟨(hdeg a).1,?_⟩
    exact (Nat.mul_le_mul_right (2*r-3) (Nat.pow_le_pow_left (hrow a) 2)).trans_lt
      (hdeg₀ (f₁ a)).2
  · exact column_card_le_of_subrelation hfi hsub'
  · change (∑ a : C₀, (row R (f₀ a)).card) ≤ (∑ a : C, (row Q a).card) +
      4*lightCount (fun a : C₀ => R (f₀ a)) at hE₁
    nlinarith only [hE₀,hE₁,hL₀]
  · nlinarith only [hL₁,hL₀]

#print axioms column_card_le_of_subrelation
#print axioms punctured_column_four_free
#print axioms normalize
end Erdos713ThetaFinalNormalization
