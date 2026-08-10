import FormalConjectures.Util.ProblemImports

def badProof (n : Nat) : False := by
  have h : n / 2 < n := by
    by_cases hn : n = 0
    · subst n; omega
    · exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by norm_num : 1 < 2)
  exact badProof (n/2)
termination_by n

theorem tfalse : False := badProof 1
#print axioms tfalse
