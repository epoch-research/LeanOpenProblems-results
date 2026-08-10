import FormalConjectures.Util.ProblemImports

partial def negToP (P : Prop) (h : ¬ P) : P := False.elim (h (negToP P h))

theorem dneLoop (P : Prop) (h : ¬¬P) : P := negToP P (fun hp => h (fun _ => hp))

theorem arb (P : Prop) : P := Classical.byContradiction (fun hn => hn (negToP P hn))
#print axioms negToP
#print axioms arb
