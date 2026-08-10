import FormalConjectures.Util.ProblemImports

-- These should all fail or be impossible if the instance database is consistent.
#synth Subsingleton PUnit
#synth Nontrivial PUnit
#synth Subsingleton Unit
#synth Nontrivial Unit
#synth Subsingleton Empty
#synth Nontrivial Empty
#synth Subsingleton PEmpty
#synth Nontrivial PEmpty
#synth Subsingleton True
#synth Nontrivial True
#synth Subsingleton False
#synth Nontrivial False
#synth Subsingleton Nat
#synth Nontrivial Nat
