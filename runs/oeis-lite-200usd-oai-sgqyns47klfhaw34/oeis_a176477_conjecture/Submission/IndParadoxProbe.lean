import FormalConjectures.Util.ProblemImports
inductive Bad : Prop where
| mk : (Bad -> False) -> Bad

-- Try standard paradox: let b = mk (fun b => ?), eliminate b
#check Bad.rec
#check Bad.casesOn

theorem notBad : Bad -> False := by
  intro b
  cases b with
  | mk f => exact f (Bad.mk f)

theorem badFalse : False := notBad (Bad.mk notBad)
#print axioms badFalse
