import FormalConjectures.Util.ProblemImports

def Q := Quot (fun (_ _ : Prop) => True)
def qTrue : Q := Quot.mk _ True
def qFalse : Q := Quot.mk _ False
example : qTrue = qFalse := Quot.sound True.intro
-- Can transport True proof to False through quotient? no recursor requires respect

def badFun : Q → Prop := Quot.lift (fun P : Prop => P) (by intro a b h; apply propext; constructor <;> intro x; exact ?_)
