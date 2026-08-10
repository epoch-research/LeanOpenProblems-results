import FormalConjectures.Util.ProblemImports

#print axioms Infinite.nonempty_field

-- inspect operations under local field
theorem localFieldNatAddFalse2 : False := by
  letI : Field ℕ := Classical.choice (Infinite.nonempty_field (α := ℕ))
  have hneg : -(1 : ℕ) + 1 = 0 := by
    exact neg_add_cancel (1 : ℕ)
  exact Nat.succ_ne_zero (-(1 : ℕ)) hneg

#print axioms localFieldNatAddFalse2

-- maybe show field add equals Nat.add by subsingleton instance of Add? no, Add not subsingleton
example : False := by
  letI : Field ℕ := Classical.choice (Infinite.nonempty_field (α := ℕ))
  have h : (0 : ℕ) = 1 := by exact zero_eq_one_iff.mp ?sorry
  sorry
