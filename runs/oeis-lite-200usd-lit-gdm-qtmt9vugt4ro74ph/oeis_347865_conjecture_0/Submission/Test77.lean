import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

instance (n : Nat) : Inhabited (PLift (Nonempty (a n > 0)) ⊕ Unit) :=
  ⟨Sum.inr ()⟩

opaque get_nonempty_or_unit (n : Nat) (hn : n ≥ 745) : PLift (Nonempty (a n > 0)) ⊕ Unit
