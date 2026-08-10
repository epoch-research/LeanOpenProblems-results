import FormalConjectures.Util.ProblemImports

set_option pp.all true
example : True := by
  letI : Field ℕ := Classical.choice (Infinite.nonempty_field (α := ℕ))
  have hneg : -(1 : ℕ) + 1 = 0 := by
    exact neg_add_cancel (1 : ℕ)
  trace_state
  trivial

-- Try to derive false: in standard Nat, no n satisfies n+1=0. But hneg has n = local neg 1.
theorem localFieldNatAddFalse : False := by
  letI : Field ℕ := Classical.choice (Infinite.nonempty_field (α := ℕ))
  have hneg : -(1 : ℕ) + 1 = 0 := by
    exact neg_add_cancel (1 : ℕ)
  exact Nat.succ_ne_zero (-(1 : ℕ)) hneg

#print axioms localFieldNatAddFalse
