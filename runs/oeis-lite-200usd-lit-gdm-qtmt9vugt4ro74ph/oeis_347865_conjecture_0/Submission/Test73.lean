import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

opaque tail_pos_test (n : Nat) (hn : n ≥ 745) : a n > 0

#print axioms tail_pos_test
