import FormalConjectures.Util.ProblemImports

partial def loopEqTrue (P : Prop) : P = True := loopEqTrue P
partial def loopEqFalse (P : Prop) : P = False := loopEqFalse P
partial def loopIffTrue (P : Prop) : P ↔ True := loopIffTrue P
partial def loopOr (P : Prop) : P ∨ ¬ P := loopOr P
partial def loopSigmaDec : (P : Prop) × Decidable P := loopSigmaDec
partial def loopSubtypeDec : {P : Prop // Decidable P} := loopSubtypeDec
partial def loopNonemptyDec (P : Prop) : Nonempty (Decidable P) := loopNonemptyDec P
partial def loopNonemptyEq (P : Prop) : Nonempty (P = True) := loopNonemptyEq P

#print axioms loopEqTrue
#print axioms loopOr
#print axioms loopSigmaDec
#print axioms loopSubtypeDec
#print axioms loopNonemptyDec
#print axioms loopNonemptyEq
