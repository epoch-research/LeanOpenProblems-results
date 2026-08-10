import FormalConjectures.Util.ProblemImports
inductive Co (P : Prop) where | delay : (Unit → Co P) → Co P
partial def co (P : Prop) : Co P := Co.delay (fun _ => co P)
#check co
#print axioms co
