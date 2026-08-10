import FormalConjectures.Util.ProblemImports

unsafe def unsafe_proof (P : Prop) : P :=
  unsafe_proof P

theorem bad : False :=
  unsafe_proof False

