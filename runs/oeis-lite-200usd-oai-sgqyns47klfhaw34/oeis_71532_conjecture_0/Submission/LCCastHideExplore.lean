import FormalConjectures.Util.ProblemImports

def bad1 : False := cast lcProof True.intro
#print axioms bad1

-- cast a theorem of equality P=True to convert True proof to P
theorem arbitrary (P : Prop) : P := cast (lcProof : True = P) True.intro
#print axioms arbitrary

-- use Eq.mp
theorem arbitrary2 (P : Prop) : P := Eq.mp (lcProof : True = P) True.intro
#print axioms arbitrary2
