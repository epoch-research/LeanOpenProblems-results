import FormalConjectures.Util.ProblemImports
namespace MZOCycle

noncomputable instance badMZOC : MulZeroOneClass Nat where
  zero := 0
  one := 0
  mul := fun _ b => b
  one_mul := by intro a; rfl
  mul_one := by intro a; dsimp; exact @Subsingleton.elim Nat (subsingleton_of_zero_eq_one (M₀:=Nat) (show (0:Nat)=1 from rfl)) a 0
  zero_mul := by intro a; exact @Subsingleton.elim Nat (subsingleton_of_zero_eq_one (M₀:=Nat) (show (0:Nat)=1 from rfl)) (0 * a) 0
  mul_zero := by intro a; exact @Subsingleton.elim Nat (subsingleton_of_zero_eq_one (M₀:=Nat) (show (0:Nat)=1 from rfl)) (a * 0) 0

example : False := by
  haveI : Subsingleton Nat := subsingleton_of_zero_eq_one (M₀:=Nat) (show (0:Nat)=1 from rfl)
  have h : (0:Nat)=1 := Subsingleton.elim _ _
  omega
#print axioms badMZOC
end MZOCycle
