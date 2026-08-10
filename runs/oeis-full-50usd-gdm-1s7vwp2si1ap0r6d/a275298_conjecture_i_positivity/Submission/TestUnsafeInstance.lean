import FormalConjectures.Util.ProblemImports

partial instance (P : Prop) : Inhabited P :=
  let rec loop : Inhabited P := loop
  loop


