import Mathlib

def MyProp : Prop := 1 + 1 = 3

instance : Inhabited (MyProp → True) where
  default := fun _ => True.intro

opaque my_theorem : MyProp → True

#print axioms my_theorem
