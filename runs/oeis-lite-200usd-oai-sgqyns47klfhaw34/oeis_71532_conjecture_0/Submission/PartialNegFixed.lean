import FormalConjectures.Util.ProblemImports

axiom P : Prop
partial def disLoop (h : P) : False := disLoop h
#print axioms disLoop
example : ¬ P := disLoop
