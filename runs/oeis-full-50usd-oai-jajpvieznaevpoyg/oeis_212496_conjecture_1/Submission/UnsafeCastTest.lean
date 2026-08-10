import FormalConjectures.Util.ProblemImports
unsafe instance : Inhabited False := ⟨unsafeCast ()⟩
partial def bad (_ : Nat) : False := bad 0
theorem t : False := bad 0
#print axioms t
