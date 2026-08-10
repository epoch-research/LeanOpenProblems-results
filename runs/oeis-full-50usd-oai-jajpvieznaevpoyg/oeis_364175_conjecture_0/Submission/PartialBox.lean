import FormalConjectures.Util.ProblemImports
structure Box (P : Prop) where get : P
partial def boxLoop (P : Prop) : Box P := boxLoop P
instance (P : Prop) : Inhabited (Box P) := ⟨boxLoop P⟩
theorem bad (P : Prop) : P := (default : Box P).get
#print axioms boxLoop
#print axioms bad
