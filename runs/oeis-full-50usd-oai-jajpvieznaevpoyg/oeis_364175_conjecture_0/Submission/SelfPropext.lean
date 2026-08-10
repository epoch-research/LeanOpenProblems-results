import FormalConjectures.Util.ProblemImports

theorem t (P Q : Prop) (hp : P) : Q := by
  let rec hEq : P = Q := propext ⟨(fun _ => cast hEq hp), (fun _ => hp)⟩
  exact cast hEq hp
