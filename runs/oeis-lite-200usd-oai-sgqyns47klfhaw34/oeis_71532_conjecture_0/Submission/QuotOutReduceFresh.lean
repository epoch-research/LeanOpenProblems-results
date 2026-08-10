import FormalConjectures.Util.ProblemImports

def r (P Q : Prop) := P ↔ Q
#reduce Quot.out (Quot.mk r True)
#eval (Lean.Syntax.missing) -- dummy
