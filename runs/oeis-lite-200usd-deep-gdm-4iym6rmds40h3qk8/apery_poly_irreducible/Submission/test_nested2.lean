import FormalConjectures.Util.ProblemImports

structure F (α : Type) : Type where
  mk :: val : α → Prop

inductive T : Type
| mk : F T → T

