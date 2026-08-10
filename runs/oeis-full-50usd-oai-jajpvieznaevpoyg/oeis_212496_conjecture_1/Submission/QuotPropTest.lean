import FormalConjectures.Util.ProblemImports

def Q := Quot (s := ⟨fun _ _ : Prop => True, by intro; trivial, by intro; trivial, by intro; trivial⟩)

def F (q : Q) : Prop := Quot.lift (fun p : Prop => p) (by intro a b h; exact propext ?_) q
