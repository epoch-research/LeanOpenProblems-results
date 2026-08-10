import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 1000
lemma possible_fin (s : Fin 588) :
    s.val % 4 = 3 → 2^s.val ≡ s.val + 13573 [MOD 49] →
    s.val = 183 ∨ s.val = 415 ∨ s.val = 431 := by
  fin_cases s <;> decide
