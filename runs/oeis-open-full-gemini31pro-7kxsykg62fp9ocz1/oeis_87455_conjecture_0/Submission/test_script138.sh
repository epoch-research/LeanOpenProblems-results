#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

-- Can we use `Classical.choice` without `Nonempty`?
-- No.
INNER_EOF
lake build Submission.Spec
