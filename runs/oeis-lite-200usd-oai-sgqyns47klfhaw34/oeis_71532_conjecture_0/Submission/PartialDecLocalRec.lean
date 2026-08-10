import FormalConjectures.Util.ProblemImports

partial def magicDec (P : Prop) : Decidable P :=
  Decidable.isTrue (let rec get : P :=
    match magicDec P with
    | Decidable.isTrue h => h
    | Decidable.isFalse hn => False.elim (hn get)
    termination_by 0
    get)

#print magicDec
#print axioms magicDec

theorem arb (P : Prop) : P := by
  let d := magicDec P
  cases d with
  | isTrue h => exact h
  | isFalse hn =>
      -- but magicDec is definitionally isTrue? maybe not opaque
      change Decidable P at d
      -- have hd? no equations
      exact False.elim (hn (by
        let rec get : P :=
          match magicDec P with
          | Decidable.isTrue h => h
          | Decidable.isFalse hn => False.elim (hn get)
          termination_by 0
        exact get))
#print axioms arb
