axiom sequence_s_int : Int → Nat

theorem test (h : False) : sequence_s_int 0 = 0 := by contradiction
#print axioms test
