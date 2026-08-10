import FormalConjectures.Util.ProblemImports

partial def infLoop (α : Sort u) : Infinite α := infLoop α
partial def nontrivLoop (α : Type u) : Nontrivial α := nontrivLoop α
partial def subsingLoop (α : Type u) : Subsingleton α := subsingLoop α
partial def finiteLoop (α : Sort u) : Finite α := finiteLoop α

#print axioms infLoop
#print axioms nontrivLoop
#print axioms subsingLoop
#print axioms finiteLoop
