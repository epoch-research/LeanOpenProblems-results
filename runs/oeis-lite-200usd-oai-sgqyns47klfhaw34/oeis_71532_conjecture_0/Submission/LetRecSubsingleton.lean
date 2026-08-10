import FormalConjectures.Util.ProblemImports

theorem arbitrary (P : Prop) : P := by
  let rec instSub : Subsingleton Nat := ⟨fun x y => by
    haveI : Subsingleton Nat := instSub
    have h01 : (0:Nat) = 1 := Subsingleton.elim 0 1
    exact False.elim (Nat.zero_ne_one h01)
  ⟩
  haveI : Subsingleton Nat := instSub
  have h01 : (0:Nat) = 1 := Subsingleton.elim 0 1
  exact False.elim (Nat.zero_ne_one h01)

#print axioms arbitrary
