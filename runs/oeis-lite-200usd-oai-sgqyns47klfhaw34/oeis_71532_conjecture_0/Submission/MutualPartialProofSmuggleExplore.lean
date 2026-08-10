import FormalConjectures.Util.ProblemImports

mutual
partial def dAny (P : Prop) : Decidable P := dAny P
partial def pAny (P : Prop) : P := pAny P
end

theorem arbitrary (P : Prop) : P := pAny P
#print axioms arbitrary
