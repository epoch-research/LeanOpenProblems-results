import FormalConjectures.Util.ProblemImports
#synth Inhabited (Fact False)
#synth Nonempty (Fact False)
#synth Inhabited False
#synth Nonempty False
#synth Inhabited {x : ℕ // False}
#synth Nonempty {x : ℕ // False}
#synth Unique False
#synth Subsingleton False
#synth Subsingleton (Fact False)
example : False := (default : Fact False).out
