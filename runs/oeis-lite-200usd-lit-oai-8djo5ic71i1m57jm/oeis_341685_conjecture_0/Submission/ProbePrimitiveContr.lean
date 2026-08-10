import FormalConjectures.Util.ProblemImports

example : False := by
  have h := one_isPrimitive_iff (S := (∅ : Set ℕ))
  simp at h

example : False := by
  have hp : Nat.Prime 2 := by norm_num
  have h := prime_isPrimitive_iff (S := ({4} : Set ℕ)) hp
  -- 2 ∉ {4}; RHS? no proper divisor in S? 4? 2 ∣ 4 and 2<4, so false
  simp at h
