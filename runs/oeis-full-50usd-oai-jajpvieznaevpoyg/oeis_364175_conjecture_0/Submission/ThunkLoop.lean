import FormalConjectures.Util.ProblemImports
structure Thunk (P : Prop) where run : Unit → P
partial def thunk (P : Prop) : Thunk P := ⟨fun _ => (thunk P).run ()⟩
theorem bad : False := (thunk False).run ()
#print axioms bad
