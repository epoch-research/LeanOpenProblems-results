#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

-- Is there any implicit parameter?
-- `A087455_satisfies_Benfords_law` is just `Prop`.
INNER_EOF
lake build Submission.Spec
