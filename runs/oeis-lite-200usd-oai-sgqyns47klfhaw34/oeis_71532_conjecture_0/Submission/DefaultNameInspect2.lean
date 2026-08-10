import FormalConjectures.Util.ProblemImports

def g (x : Nat := 3) (y : Nat := 4) := x+y
#print g
#check g ()
#check g
#eval g
#eval g 10
#eval g (y:=7)
