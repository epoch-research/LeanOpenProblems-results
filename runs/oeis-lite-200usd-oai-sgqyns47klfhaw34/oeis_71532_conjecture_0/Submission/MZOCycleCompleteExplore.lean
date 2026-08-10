import FormalConjectures.Util.ProblemImports

namespace MZOCycle
noncomputable instance badMZOC : MulZeroOneClass Nat where
  zero := 0
  one := 0
  mul := fun _ _ => 0
  one_mul := by
    intro a
    let s : Subsingleton Nat := @subsingleton_of_zero_eq_one Nat badMZOC rfl
    exact @Subsingleton.elim Nat s (0) a
  mul_one := by
    intro a
    let s : Subsingleton Nat := @subsingleton_of_zero_eq_one Nat badMZOC rfl
    exact @Subsingleton.elim Nat s (0) a
  zero_mul := by intro a; rfl
  mul_zero := by intro a; rfl

noncomputable theorem natSubsingleton : Subsingleton Nat := @subsingleton_of_zero_eq_one Nat badMZOC rfl

theorem bad : False := by
  have h : (0:Nat) = 1 := @Subsingleton.elim Nat natSubsingleton 0 1
  omega

#print axioms bad
end MZOCycle
