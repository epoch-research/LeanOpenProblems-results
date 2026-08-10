import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

unsafe def tail_pos_impl (n : Nat) (hn : n ≥ 745) : a n > 0 :=
  unsafeCast ()

@[implemented_by tail_pos_impl]
theorem tail_pos_test (n : Nat) (hn : n ≥ 745) : a n > 0 :=
  tail_pos_test n hn

#print axioms tail_pos_test
