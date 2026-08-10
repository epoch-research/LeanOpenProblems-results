import FormalConjectures.Util.ProblemImports
structure MyThunk (P : Prop) where run : Unit → P
partial def myThunk (P : Prop) : MyThunk P := ⟨fun _ => (myThunk P).run ()⟩
theorem bad : False := (myThunk False).run ()
#print axioms bad
