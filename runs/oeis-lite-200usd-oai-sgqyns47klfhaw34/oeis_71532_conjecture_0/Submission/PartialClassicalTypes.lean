import FormalConjectures.Util.ProblemImports
axiom P : Prop
partial def sumEM (P : Prop) : Sum P (P → False) := sumEM P
#print axioms sumEM
partial def psumEM (P : Prop) : PSum P (P → False) := psumEM P
#print axioms psumEM
partial def sigmaEM (P : Prop) : Σ b : Bool, if b then P else (P → False) := sigmaEM P
#print axioms sigmaEM
