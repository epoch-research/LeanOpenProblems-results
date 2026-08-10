import FormalConjectures.Util.ProblemImports
axiom P : Prop
-- Can a theorem with an autoImplicit hidden parameter print as P?
theorem foo {h : False} : P := False.elim h
#check foo
#print foo
