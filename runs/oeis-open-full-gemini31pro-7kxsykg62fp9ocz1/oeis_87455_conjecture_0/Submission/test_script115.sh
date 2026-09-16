#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

-- What if I use `#check` and see what it is?
#print A087455_satisfies_Benfords_law
INNER_EOF
lake build Submission.Spec
