#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

-- Is there a way to define a constant using `axiom` but giving it a value? No.
INNER_EOF
lake build Submission.Spec
