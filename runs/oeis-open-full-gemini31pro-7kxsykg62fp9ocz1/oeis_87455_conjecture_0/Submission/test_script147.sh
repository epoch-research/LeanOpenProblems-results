#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

-- What if I use `#print` on `A087455_satisfies_Benfords_law` to see if it's overriden?
-- It's an axiom.
INNER_EOF
lake build Submission.Spec
