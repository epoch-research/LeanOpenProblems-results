import FormalConjectures.Util.ProblemImports
axiom P : Prop
structure Wrap where val : P deriving Inhabited
example : P := (default : Wrap).val
#print axioms instInhabitedWrap
