import FormalConjectures.Util.ProblemImports

inductive Bad : Bool → Type where
| mk : Bad true
  deriving Inhabited, Nonempty

#synth Inhabited (Bad true)
#synth Nonempty (Bad true)
#synth Inhabited (Bad false)
#synth Nonempty (Bad false)

theorem bad : False := by
  let x : Bad false := default
  cases x
#print axioms bad
