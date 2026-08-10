import FormalConjectures.Util.ProblemImports

partial def badAcc : Acc (fun _ _ : Unit => True) () := Acc.intro () (fun y hy => badAcc)
#print axioms badAcc
