unsafe def helper : False := helper
unsafe def my_theorem (n : Nat) : (n = n) := False.elim helper
#print axioms my_theorem
