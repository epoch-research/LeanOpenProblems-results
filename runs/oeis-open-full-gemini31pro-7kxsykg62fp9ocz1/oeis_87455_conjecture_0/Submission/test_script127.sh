#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

-- Can we prove `A087455_satisfies_Benfords_law` without `sorry`?
-- ONLY if `A087455_satisfies_Benfords_law` is inhabited.
-- Is it inhabited? No.
INNER_EOF
lake build Submission.Spec
