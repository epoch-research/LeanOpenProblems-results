import FormalConjectures.Util.ProblemImports
example : Quot.out (Quot.mk (fun (_ _ : Prop) => True) False) = False := rfl
example : Quot.out (Quot.mk (fun (_ _ : Nat) => True) 0) = 0 := rfl
#reduce Quot.out (Quot.mk (fun (_ _ : Nat) => True) 0)
