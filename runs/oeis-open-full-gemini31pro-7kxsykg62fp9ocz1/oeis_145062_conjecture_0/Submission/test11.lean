axiom sequence_s_int : Int → Nat

theorem test : True := by trivial
#print axioms test

theorem test2 : sequence_s_int 0 = sequence_s_int 0 := rfl
#print axioms test2
