import FormalConjectures.Util.ProblemImports
def R (P Q : Prop) : Prop := True
def val (q : Quot R) : Prop := Quot.inductionOn q (fun P : Prop => P)
