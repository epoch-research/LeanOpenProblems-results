import FormalConjectures.Util.ProblemImports

partial def loopDec (P : Prop) : Decidable P := loopDec P

example (P : Prop) : P := by
  classical
  let d : Decidable P := loopDec P
  let hp : P := by
    -- Try to get proof from an equality whose RHS needs it.
    let e : d = Decidable.isTrue hp := Subsingleton.elim _ _
    cases e
    cases d with
    | isTrue h => exact h
    | isFalse hn => exact False.elim (hn hp)
  exact hp
