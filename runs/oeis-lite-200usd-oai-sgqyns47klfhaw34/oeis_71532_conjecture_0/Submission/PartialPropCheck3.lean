import FormalConjectures.Util.ProblemImports

partial def L (_ : Unit) : Prop := ¬ L ()
#check L
#check L.eq_def
#check L._unary
#check L.match_1
#print L
#print prefix L
