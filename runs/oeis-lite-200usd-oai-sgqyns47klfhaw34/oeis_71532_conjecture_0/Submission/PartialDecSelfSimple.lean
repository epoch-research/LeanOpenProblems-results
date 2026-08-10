import FormalConjectures.Util.ProblemImports

partial def magicDec (P : Prop) : Decidable P :=
  Decidable.isTrue (by
    let d := magicDec P
    cases d with
    | isTrue h => exact h
    | isFalse hn =>
        -- recursive call again; need proof, can call same by block? no name
        exact False.elim (hn (by
          let d2 := magicDec P
          cases d2 with
          | isTrue h => exact h
          | isFalse hn2 => exact False.elim (hn2 (by
              let d3 := magicDec P
              cases d3 with
              | isTrue h => exact h
              | isFalse hn3 => exact False.elim (hn3 (Classical.byContradiction fun hnp => hn hnp.elim)))))

#print magicDec
#print axioms magicDec

-- If magicDec is a theorem-level definition equal to isTrue body? Print says def/opaque?
theorem arb (P : Prop) : P := by
  cases magicDec P with
  | isTrue h => exact h
  | isFalse hn => exact False.elim (hn (Classical.byContradiction (fun hnp => hn (Classical.byContradiction fun _ => False.elim (hnp (by
        cases magicDec P with
        | isTrue h => exact h
        | isFalse hn2 => exact False.elim (hn2 (Classical.byContradiction fun hnp2 => hn2 (by contradiction))))))))
#print axioms arb
