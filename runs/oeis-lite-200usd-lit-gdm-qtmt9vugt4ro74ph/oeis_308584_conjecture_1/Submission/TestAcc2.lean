import FormalConjectures.Util.ProblemImports

open Nat Finset

def bad_rel (x y : ℕ) : Prop := True

partial def my_acc (x : ℕ) : Acc bad_rel x :=
  @Acc.intro ℕ bad_rel x (fun y (h : bad_rel y x) => my_acc y)

#print axioms my_acc
