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

-- Let's define a new axiom? No.
-- Is it possible to use `cast` with a proof of `True = A087455_satisfies_Benfords_law`?
-- How can I prove `True = A087455_satisfies_Benfords_law`?
-- By `propext`? `propext` requires `True ↔ A087455_satisfies_Benfords_law`.
-- Which requires `A087455_satisfies_Benfords_law`.
-- So it's equivalent.

theorem oeis_87455_conjecture_0.disproof : ¬ (type_of% @oeis_87455_conjecture_0) := by
  sorry
INNER_EOF
lake build Submission.Spec
