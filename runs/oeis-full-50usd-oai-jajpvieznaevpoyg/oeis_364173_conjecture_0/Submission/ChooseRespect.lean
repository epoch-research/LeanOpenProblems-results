import FormalConjectures.Util.ProblemImports

#check Classical.indefiniteDescription
#check Classical.choose
#print Classical.choose
#print Classical.indefiniteDescription

-- If predicates are extensionally equal, choose respects them.
example {α : Sort u} {p q : α → Prop} (h : p = q) (hp : ∃ x, p x) (hq : ∃ x, q x) :
    Classical.choose hp = Classical.choose hq := by
  subst h
  congr

-- If existential props are equal only, it should not.
example {α : Sort u} {p q : α → Prop} (h : (∃ x, p x) = (∃ x, q x)) (hp : ∃ x, p x) (hq : ∃ x, q x) :
    True := by
  trivial
