import FormalConjectures.Util.ProblemImports

-- Try a few small direct contradictions with the custom decidable instance
example : ¬ Nat.IsPerfectPower 2 := by native_decide
example : ¬ Nat.IsPerfectPower 3 := by native_decide
example : Nat.IsPerfectPower 4 := by native_decide
example : Nat.IsPerfectPower 8 := by native_decide
example : Nat.IsPerfectPower 9 := by native_decide
example : ¬ Nat.IsPerfectPower 12 := by native_decide
example : Nat.IsPerfectPower 16 := by native_decide

-- See if theorem gives wrong side for any selected n
example : False := by
  have h : Nat.IsPerfectPower 2 := by decide +native
  rcases h with ⟨k,m,hk,hm,hpow⟩
  interval_cases k <;> interval_cases m <;> norm_num at *
