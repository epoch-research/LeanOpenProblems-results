import FormalConjectures.Util.ProblemImports

-- Can local recursive definitions manufacture an Inhabited proposition?
example (P : Prop) : P := by
  let rec inst : Inhabited P := ⟨inst.default⟩
  exact inst.default
