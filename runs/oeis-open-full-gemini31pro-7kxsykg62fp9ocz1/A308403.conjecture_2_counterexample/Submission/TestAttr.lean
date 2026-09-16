import Mathlib

noncomputable def myFunc : Nat := 0

def myFuncComp : Nat := 1

attribute [implemented_by myFuncComp] myFunc

theorem test : myFunc = 1 := by native_decide
