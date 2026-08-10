import FormalConjectures.Util.ProblemImports

namespace WrapNatMZOCycle

inductive WNat where
| mk : Nat → WNat

def toNat : WNat → Nat | .mk n => n
def ofNat (n : Nat) : WNat := .mk n

def equivNat : WNat ≃ Nat where
  toFun := toNat
  invFun := ofNat
  left_inv := by intro x; cases x; rfl
  right_inv := by intro n; rfl

noncomputable instance badMZOC : MulZeroOneClass WNat where
  zero := WNat.mk 0
  one := WNat.mk 0
  mul := fun _ _ => WNat.mk 0
  one_mul := by
    intro a
    let s : Subsingleton WNat := @subsingleton_of_zero_eq_one WNat badMZOC rfl
    exact @Subsingleton.elim WNat s (WNat.mk 0) a
  mul_one := by
    intro a
    let s : Subsingleton WNat := @subsingleton_of_zero_eq_one WNat badMZOC rfl
    exact @Subsingleton.elim WNat s (WNat.mk 0) a
  zero_mul := by intro a; rfl
  mul_zero := by intro a; rfl

theorem wnatSubsingleton : Subsingleton WNat :=
  @subsingleton_of_zero_eq_one WNat badMZOC rfl

theorem natSubsingleton : Subsingleton Nat := by
  constructor
  intro n m
  have h : (equivNat.symm n) = (equivNat.symm m) := @Subsingleton.elim WNat wnatSubsingleton _ _
  exact congrArg equivNat h

theorem bad : False := by
  have h : (0:Nat) = 1 := @Subsingleton.elim Nat natSubsingleton 0 1
  omega

#print axioms bad
end WrapNatMZOCycle
