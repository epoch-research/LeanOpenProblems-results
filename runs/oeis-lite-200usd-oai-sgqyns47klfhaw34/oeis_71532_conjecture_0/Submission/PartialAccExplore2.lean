import FormalConjectures.Util.ProblemImports

partial def badAcc (_ : Unit) : Acc (fun _ _ : Unit => True) () := Acc.intro () (fun y hy => badAcc ())
#print axioms badAcc
