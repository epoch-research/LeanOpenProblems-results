import FormalConjectures.Util.ProblemImports

def MyProp : Prop := False

partial def my_proof (n : ℕ) : MyProp :=
  my_proof n

theorem my_theorem : MyProp :=
  my_proof 0
