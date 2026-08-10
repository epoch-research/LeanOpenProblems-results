import FormalConjectures.Util.ProblemImports
axiom P : Prop
structure Wrap where val : P
noncomputable instance instWrap : Inhabited Wrap where
  default := ⟨(default : Wrap).val⟩
#print axioms instWrap
example : P := (default : Wrap).val
