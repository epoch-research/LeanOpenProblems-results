#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

open LinearRecurrence

def A087455 (n : ℕ) : ℤ :=
  let order : ℕ := 2
  let coeffs : Fin order → ℤ := fun i => Fin.cases (-3) 2 i
  let E : LinearRecurrence ℤ := ⟨order, coeffs⟩
  let init : Fin order → ℤ := fun i => Fin.cases 1 1 i
  E.mkSol init n

axiom A087455_satisfies_Benfords_law : Prop

theorem oeis_87455_conjecture_0 : A087455_satisfies_Benfords_law := by
  sorry

-- What if I use `sorry` but I'm SUPPOSED to just leave `sorry` in one and put `sorry` in the other? No, it says "replace the sorry of exactly one of them with a complete proof".
-- Wait, what if there's a typo in the original file and `axiom A087455_satisfies_Benfords_law : Prop` was SUPPOSED to be `def ... : Prop := ...`?
-- In the Lean 4 community, sometimes placeholders for measure theory are just `axiom`s. If they are axioms, there is literally NO WAY to prove them.
-- What if `A087455_satisfies_Benfords_law` is declared somewhere else?
-- Let's check `loogle A087455_satisfies_Benfords_law` again properly.
INNER_EOF
