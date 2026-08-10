import FormalConjectures.Util.ProblemImports

namespace BadNatMZOCycle

def BadNat := Nat

noncomputable instance badMZOC : MulZeroOneClass BadNat where
  zero := (0 : Nat)
  one := (0 : Nat)
  mul := fun _ _ => (0 : Nat)
  one_mul := by
    intro a
    let s : Subsingleton BadNat := @subsingleton_of_zero_eq_one BadNat badMZOC rfl
    exact @Subsingleton.elim BadNat s (0 : BadNat) a
  mul_one := by
    intro a
    let s : Subsingleton BadNat := @subsingleton_of_zero_eq_one BadNat badMZOC rfl
    exact @Subsingleton.elim BadNat s (0 : BadNat) a
  zero_mul := by intro a; rfl
  mul_zero := by intro a; rfl

noncomputable theorem badSubsingleton : Subsingleton BadNat :=
  @subsingleton_of_zero_eq_one BadNat badMZOC rfl

theorem natSubsingleton : Subsingleton Nat := by
  change Subsingleton BadNat
  exact badSubsingleton

theorem bad : False := by
  have h : (0:Nat) = 1 := @Subsingleton.elim Nat natSubsingleton 0 1
  omega

#print axioms bad
end BadNatMZOCycle
