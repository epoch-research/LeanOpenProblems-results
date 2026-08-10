import FormalConjectures.Util.ProblemImports

partial def loopTrunc (P : Prop) : Trunc P := loopTrunc P
theorem arbT (P : Prop) : P := Trunc.out (loopTrunc P)
#print axioms loopTrunc
#print axioms arbT

partial def loopErased (P : Prop) : Erased P := loopErased P
theorem arbE (P : Prop) : P := Erased.out_proof (loopErased P)
#print axioms loopErased
#print axioms arbE

partial def loopPart (P : Prop) : Part P := loopPart P
-- Part.unwrap unsafe? no safe theorem to extract without Dom
#print axioms loopPart
