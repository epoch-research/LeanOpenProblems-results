import FormalConjecturesUtil
import Submission.C8CommutingGeneratorSets

/-! Additive affine generator curves and a four-parameter obstruction.
This is auxiliary work, not a proof of Erdős 713. -/
open SimpleGraph
namespace Erdos713C8AdditiveAffine
open Erdos713C8CommutingDifferences
set_option maxHeartbeats 2000000

section Inverse
variable {G I : Type*} [Group G]

/-- Replacing all generators by their inverses swaps the two shores. -/
def inverseGraphIso (g : I → G) : graph g ≃g graph (fun i => (g i)⁻¹) where
  toEquiv := Equiv.sumComm G G
  map_rel_iff' := by
    intro v w
    cases v with
    | inl p =>
      cases w with
      | inl q => rfl
      | inr l =>
        change (∃ i, p=l*(g i)⁻¹) ↔ ∃ i, l=p*g i
        constructor
        · rintro ⟨i,h⟩; refine ⟨i,?_⟩; rw [h]; simp [mul_assoc]
        · rintro ⟨i,h⟩; refine ⟨i,?_⟩; rw [h]; simp [mul_assoc]
    | inr l =>
      cases w with
      | inl p =>
        change (∃ i, p=l*(g i)⁻¹) ↔ ∃ i, l=p*g i
        constructor
        · rintro ⟨i,h⟩; refine ⟨i,?_⟩; rw [h]; simp [mul_assoc]
        · rintro ⟨i,h⟩; refine ⟨i,?_⟩; rw [h]; simp [mul_assoc]
      | inr q => rfl

end Inverse

variable {K : Type*} [Field K]

/-- An invertible affine transformation, with nonzero slope. -/
def affine (a : Kˣ) (b : K) : Equiv.Perm K where
  toFun x := (a : K)*x+b
  invFun x := (a : K)⁻¹*(x-b)
  left_inv x := by field_simp; ring
  right_inv x := by field_simp; ring

@[simp] lemma affine_apply (a : Kˣ) (b x : K) : affine a b x = (a : K)*x+b := rfl
@[simp] lemma affine_inv_apply (a : Kˣ) (b x : K) :
    (affine a b)⁻¹ x = (a : K)⁻¹*(x-b) := rfl

def curve (f : K →+ K) (a : Kˣ) : Equiv.Perm K := affine a (f a)

lemma curve_injective (f : K →+ K) : Function.Injective (curve f) := by
  intro a b h
  apply Units.ext
  have h0 := congrArg (fun p : Equiv.Perm K => p 0) h
  have h1 := congrArg (fun p : Equiv.Perm K => p 1) h
  simp only [curve,affine_apply,mul_zero,zero_add,mul_one] at h0 h1
  linear_combination h1-h0

variable [CharP K 2]

lemma right_difference_apply (f : K →+ K) (a b : Kˣ) (x : K) :
    ((curve f a)⁻¹*curve f b) x = ((b : K)/(a : K))*x+f ((a : K)+(b : K))/(a : K) := by
  simp only [Equiv.Perm.mul_apply,curve,affine_apply,affine_inv_apply,
    CharTwo.sub_eq_add,map_add,div_eq_mul_inv]
  ring

/-- Right differences with the same parameter sum commute. -/
lemma right_commute (f : K →+ K) (a b c d : Kˣ)
    (hs : (a : K)+(b : K)=(c : K)+(d : K)) :
    Commute ((curve f a)⁻¹*curve f b) ((curve f c)⁻¹*curve f d) := by
  apply Equiv.ext
  intro x
  change ((curve f a)⁻¹*curve f b) (((curve f c)⁻¹*curve f d) x) =
    ((curve f c)⁻¹*curve f d) (((curve f a)⁻¹*curve f b) x)
  simp only [right_difference_apply,← hs]
  field_simp
  linear_combination (norm := ring_nf) f ((a : K)+(b : K))*hs
  reduce_mod_char!

lemma difference_ne (f : K →+ K) (a b c d : Kˣ)
    (hab : a ≠ b) (hac : a ≠ c)
    (hs : (a : K)+(b : K)=(c : K)+(d : K)) :
    (curve f a)⁻¹*curve f b ≠ (curve f c)⁻¹*curve f d := by
  intro h
  have h0 := congrArg (fun p : Equiv.Perm K => p 0) h
  have h1 := congrArg (fun p : Equiv.Perm K => p 1) h
  simp only [right_difference_apply,mul_zero,zero_add,mul_one] at h0 h1
  have hr : (b : K)/(a : K)=(d : K)/(c : K) := by linear_combination h1-h0
  have he := (div_eq_div_iff (Units.ne_zero a) (Units.ne_zero c)).mp hr
  have hprod : ((a : K)+(b : K))*((a : K)+(c : K))=0 := by
    linear_combination (norm := ring_nf) (a : K)*hs+he
    reduce_mod_char!
  exact (mul_ne_zero (fun hz => hab (Units.ext (CharTwo.add_eq_zero.mp hz)))
    (fun hz => hac (Units.ext (CharTwo.add_eq_zero.mp hz)))) hprod

lemma difference_product_ne (f : K →+ K) (a b c d : Kˣ)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hs : (a : K)+(b : K)=(c : K)+(d : K)) :
    ((curve f a)⁻¹*curve f b)*((curve f c)⁻¹*curve f d) ≠ 1 := by
  intro h
  have h0 := congrArg (fun p : Equiv.Perm K => p 0) h
  have h1 := congrArg (fun p : Equiv.Perm K => p 1) h
  change ((curve f a)⁻¹*curve f b) (((curve f c)⁻¹*curve f d) 0) = 0 at h0
  change ((curve f a)⁻¹*curve f b) (((curve f c)⁻¹*curve f d) 1) = 1 at h1
  simp only [right_difference_apply,mul_zero,zero_add,mul_one] at h0 h1
  have hr : ((b : K)/(a : K))*((d : K)/(c : K))=1 := by
    linear_combination h1-h0
  have he : (b : K)*(d : K)=(a : K)*(c : K) := by
    field_simp at hr
    exact hr
  have hprod : ((a : K)+(b : K))*((b : K)+(c : K))=0 := by
    linear_combination (norm := ring_nf) (b : K)*hs+he
    reduce_mod_char!
  exact (mul_ne_zero (fun hz => hab (Units.ext (CharTwo.add_eq_zero.mp hz)))
    (fun hz => hbc (Units.ext (CharTwo.add_eq_zero.mp hz)))) hprod

/-- This theorem also applies to arbitrary injectively parametrized
restrictions of the curve. It exhibits an actual injective C8. -/
theorem contains_at {I : Type*} (f : K →+ K) (t : I → Kˣ)
    (ht : Function.Injective t) (a b c d : I)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hs : (t a : K)+(t b : K)=(t c : K)+(t d : K)) :
    cycleGraph 8 ⊑ graph (fun i => curve f (t i)) := by
  let g := fun i => curve f (t i)
  have hinj : Function.Injective (fun i => (g i)⁻¹) :=
    inv_injective.comp ((curve_injective f).comp ht)
  have hcopy := Erdos713C8CommutingGeneratorSets.four_generator_copy
    (fun i => (g i)⁻¹) hinj a b c d hab hac had hbc hbd hcd
    (by simpa only [inv_inv] using right_commute f (t a) (t b) (t c) (t d) hs)
    (by simpa only [inv_inv] using (difference_ne f (t a) (t b) (t c) (t d)
      (ht.ne hab) (ht.ne hac) hs))
    (by simpa only [inv_inv] using (difference_product_ne f (t a) (t b) (t c) (t d)
      (ht.ne hab) (ht.ne hbc) hs))
  exact hcopy.trans (inverseGraphIso g).symm.isContained

end Erdos713C8AdditiveAffine
