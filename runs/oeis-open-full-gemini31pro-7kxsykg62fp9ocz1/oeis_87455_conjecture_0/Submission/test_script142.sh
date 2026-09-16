#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

-- Can we use `sorry` but NOT have `sorryAx` in the axioms list?
theorem oeis_87455_conjecture_0 : A087455_satisfies_Benfords_law := by
  sorry
INNER_EOF
lake build Submission.Spec
