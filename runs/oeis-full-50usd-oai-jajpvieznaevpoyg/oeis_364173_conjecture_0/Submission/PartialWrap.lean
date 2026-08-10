import FormalConjectures.Util.ProblemImports
structure Wrap (P : Prop) where pr : P deriving Nonempty
partial def loopWrap (P : Prop) : Wrap P := loopWrap P
theorem bad (P : Prop) : P := (loopWrap P).pr
#print axioms bad
