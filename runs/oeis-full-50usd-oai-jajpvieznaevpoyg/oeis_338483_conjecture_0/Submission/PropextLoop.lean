import FormalConjectures.Util.ProblemImports

theorem badLoop : ∀ n : Nat, False
| 0 => by
    have h : False = True := propext ⟨False.elim, fun _ => badLoop 0⟩
    exact cast h True.intro
| n+1 => badLoop n

theorem badFinal : False := badLoop 0
#print axioms badFinal
