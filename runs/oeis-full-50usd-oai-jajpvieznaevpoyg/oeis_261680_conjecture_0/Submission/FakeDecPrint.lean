import FormalConjectures.Util.ProblemImports
partial def fakeDec (P : Prop) : Decidable P := fakeDec P
#print fakeDec
#print axioms fakeDec
#check Classical.propDecidable
#print Classical.propDecidable
#print axioms Classical.propDecidable
