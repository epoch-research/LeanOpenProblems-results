#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

theorem oeis_87455_conjecture_0 : A087455_satisfies_Benfords_law := by
  sorry

-- Wait, can I prove it using `answer` with a configuration?
INNER_EOF
lake build Submission.Spec
