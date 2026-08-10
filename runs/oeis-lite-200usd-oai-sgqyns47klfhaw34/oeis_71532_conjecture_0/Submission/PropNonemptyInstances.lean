import FormalConjectures.Util.ProblemImports
#check Exists.nonempty
#check Classical.ofNonempty
#check Classical.propComplete
#synth Nonempty (∃ n : Nat, True)
#synth Nonempty (∀ n : Nat, True)
#synth Nonempty (True ∧ True)
#synth Nonempty (True ∨ False)
#synth Nonempty (False → True)
