import FormalConjectures.Util.ProblemImports

-- Try forward declaration via namespace? should fail.
def f (P : Prop) (p : P := g P) : P := p
where
  g (P : Prop) : P := f P

theorem arbitrary (P : Prop) : P := f P
#print axioms arbitrary
