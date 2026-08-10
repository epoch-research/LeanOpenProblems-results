import FormalConjectures.Util.ProblemImports
namespace MZOCycle
noncomputable instance badMZOC : MulZeroOneClass Nat where
  zero := 0
  one := 0
  mul := fun _ b => b
  one_mul := by intro a; rfl
  mul_one := by intro a; exact (by
    let s := @subsingleton_of_zero_eq_one Nat badMZOC ?h
    exact @Subsingleton.elim Nat s (a * 1) a)
  zero_mul := by intro a; exact (by
    let s := @subsingleton_of_zero_eq_one Nat badMZOC ?h
    exact @Subsingleton.elim Nat s (0 * a) 0)
  mul_zero := by intro a; exact (by
    let s := @subsingleton_of_zero_eq_one Nat badMZOC ?h
    exact @Subsingleton.elim Nat s (a * 0) 0)
end MZOCycle
