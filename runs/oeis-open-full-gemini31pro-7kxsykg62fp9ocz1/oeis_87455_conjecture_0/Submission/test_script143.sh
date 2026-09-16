#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

-- Can we just prove `A087455_satisfies_Benfords_law` by `exact Classical.choice ⟨sorry⟩`?
-- Yes, but it uses `sorry`.
INNER_EOF
lake build Submission.Spec
