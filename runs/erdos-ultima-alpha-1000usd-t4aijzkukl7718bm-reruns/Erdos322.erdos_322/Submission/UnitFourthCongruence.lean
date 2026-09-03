import Submission.BinaryNormBound
import Submission.LocalRootUpperBasic

/-! Bounds for unit fourth-power fibers at arbitrary positive moduli. -/
namespace Erdos322Research.UnitFourthCongruence
noncomputable section
open Finset LocalRootUpperBasic
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

/-- Every unit square-root fiber has at most twice the divisor count. -/
theorem unit_square_fiber (q : ℕ) [NeZero q] (hq : 0 < q) (v : ZMod q) :
    Fintype.card {x : ZMod q // x^2=v ∧ IsUnit x} ≤ 2*q.divisors.card := by
  classical
  let A := {x : ZMod q // x^2=v ∧ IsUnit x}
  by_cases hA : Nonempty A
  · let a : A := Classical.choice hA
    have ha : a.val.val.Coprime q := by
      apply (ZMod.isUnit_iff_coprime _ _).mp
      simpa only [ZMod.natCast_zmod_val] using a.property.2
    have hg : q.gcd (2*a.val.val) ≤ 2 := by
      rw [Nat.gcd_comm,ha.gcd_mul_right_cancel 2]
      exact Nat.gcd_le_left _ (by omega)
    let S := (Finset.range q).filter (fun r ↦ r^2 ≡ a.val.val^2 [MOD q])
    let f : A → S := fun x ↦ ⟨x.val.val,by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (ZMod.val_lt _),?_⟩
      apply (ZMod.natCast_eq_natCast_iff _ _ q).mp
      push_cast
      simp only [ZMod.natCast_zmod_val,x.property.1,a.property.1]⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      apply ZMod.val_injective
      exact congrArg (fun z : S ↦ z.val) h
    have hh := Fintype.card_le_of_injective f hf
    have hs := square_congruence_count hq hg
    rw [Fintype.card_coe] at hh
    exact hh.trans (by simpa only [mul_comm] using hs)
  · haveI : IsEmpty A := not_nonempty_iff.mp hA
    have hz : Fintype.card A=0 := Fintype.card_eq_zero
    change Fintype.card A ≤ _
    omega

/-- Iterating the quadratic estimate controls fourth roots, even at the bad prime 2. -/
theorem unit_fourth_fiber (q : ℕ) [NeZero q] (hq : 0 < q) (v : ZMod q) :
    Fintype.card {x : ZMod q // x^4=v ∧ IsUnit x} ≤ 4*q.divisors.card^2 := by
  classical
  let A := {x : ZMod q // x^4=v ∧ IsUnit x}
  let B := {x : ZMod q // x^2=v ∧ IsUnit x}
  let f : A → B := fun x ↦ ⟨x.val^2,by
    constructor
    · simpa only [← pow_mul] using x.property.1
    · exact x.property.2.pow 2⟩
  have hf (b : B) : Fintype.card {x : A // f x=b} ≤ 2*q.divisors.card := by
    let g : {x : A // f x=b} → {x : ZMod q // x^2=b.val ∧ IsUnit x} := fun x ↦
      ⟨x.val.val,congrArg Subtype.val x.property,x.val.property.2⟩
    have hg : Function.Injective g := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {x : ZMod q // x^2=b.val ∧ IsUnit x} ↦ z.val) h
    exact (Fintype.card_le_of_injective g hg).trans (unit_square_fiber q hq b.val)
  have hh := finite_fiber_bound f (2*q.divisors.card) hf
  have hb := unit_square_fiber q hq v
  calc
    Fintype.card A ≤ Fintype.card B*(2*q.divisors.card) := hh
    _ ≤ (2*q.divisors.card)*(2*q.divisors.card) := Nat.mul_le_mul_right _ hb
    _ = _ := by ring

end
end Erdos322Research.UnitFourthCongruence
