import FormalConjecturesUtil
import Submission.ThetaBalancedSplit

/-! Injectively padding a column universe preserves incidences and theta exclusion. -/
open Finset
namespace Erdos713ThetaColumnPadding
open Erdos713ThetaGram Erdos713ThetaSplit
variable {A B C : Type*}
set_option maxHeartbeats 2000000

def pad (f : B → C) (R : A → B → Prop) (a : A) (c : C) : Prop :=
  ∃ b, R a b ∧ f b = c

lemma pad_image {f : B → C} (hf : Function.Injective f) (R : A → B → Prop) (a : A) (b : B) :
    pad f R a (f b) ↔ R a b := by
  constructor
  · rintro ⟨b',hb',he⟩
    exact hf he ▸ hb'
  · exact fun hb => ⟨b,hb,rfl⟩

lemma pad_no_theta [Nonempty B] {f : B → C} (hf : Function.Injective f)
    {R : A → B → Prop} (hR : ¬ HasTheta R) : ¬ HasTheta (pad f R) := by
  classical
  apply mt (theta_of_projection (Function.invFun f) ?_ ?_) hR
  · rintro a c ⟨b,hb,rfl⟩
    simpa only [Function.leftInverse_invFun hf b] using hb
  · rintro a c d ⟨b,hb,rfl⟩ ⟨b',hb',rfl⟩ he
    rw [Function.leftInverse_invFun hf b,Function.leftInverse_invFun hf b'] at he
    exact congrArg f he

lemma pad_row_card [Fintype B] [Fintype C] {f : B → C} (hf : Function.Injective f)
    (R : A → B → Prop) (a : A) : Nat.card {c // pad f R a c} = Nat.card {b // R a b} := by
  classical
  let e : {b // R a b} ≃ {c // pad f R a c} :=
    { toFun := fun b => ⟨f b.val,b.val,b.property,rfl⟩
      invFun := fun c => ⟨c.property.choose,c.property.choose_spec.1⟩
      left_inv := by
        intro b
        apply Subtype.ext
        apply hf
        exact (show ∃ b', R a b' ∧ f b' = f b.val from ⟨b.val,b.property,rfl⟩).choose_spec.2
      right_inv := by intro c; exact Subtype.ext c.property.choose_spec.2 }
  exact (Nat.card_congr e).symm

lemma pad_column_le [Fintype A] {f : B → C} (hf : Function.Injective f)
    (R : A → B → Prop) (D : ℕ) (hD : ∀ b, Nat.card {a // R a b} ≤ D) (c : C) :
    Nat.card {a // pad f R a c} ≤ D := by
  classical
  by_cases hc : ∃ b, f b = c
  · obtain ⟨b,rfl⟩ := hc
    simpa only [pad_image hf] using hD b
  · haveI : IsEmpty {a // pad f R a c} := ⟨by rintro ⟨a,b,hb,hbc⟩; exact hc ⟨b,hbc⟩⟩
    simp

lemma pad_edge_card [Fintype A] [Fintype B] [Fintype C]
    {f : B → C} (hf : Function.Injective f) (R : A → B → Prop) :
    Nat.card {p : A × C // pad f R p.1 p.2} = Nat.card {p : A × B // R p.1 p.2} := by
  classical
  simp only [edge_card_eq_rows,pad_row_card hf]

#print axioms pad_no_theta
#print axioms pad_edge_card
end Erdos713ThetaColumnPadding
