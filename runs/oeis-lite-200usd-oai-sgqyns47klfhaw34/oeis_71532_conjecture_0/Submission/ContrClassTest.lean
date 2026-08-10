import FormalConjectures.Util.ProblemImports

example : False := by
  exact (Finite.false (α := Nat) (inferInstance : Finite Nat))

example : False := by
  exact false_of_nontrivial_of_subsingleton Nat

example : False := by
  exact CharP.false_of_nontrivial_of_char_one (R := Nat)
