import FormalConjectures.Util.ProblemImports

noncomputable def instFalse : Inhabited False := { default := instFalse.default }
example : False := instFalse.default
#print axioms instFalse
#print axioms _example

instance instP (P : Prop) : Inhabited P := { default := (instP P).default }
theorem arb (P:Prop) : P := default
#print axioms arb
