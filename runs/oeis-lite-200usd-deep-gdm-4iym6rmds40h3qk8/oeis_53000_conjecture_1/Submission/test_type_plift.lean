inductive Unsound : Prop
| base : Unsound

def f (X : Type 0) : Nat := 0

#check f (PLift Unsound)
