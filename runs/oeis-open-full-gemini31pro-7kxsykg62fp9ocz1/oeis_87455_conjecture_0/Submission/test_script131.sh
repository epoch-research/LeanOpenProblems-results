#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

-- What if I submit `answer(True)`? I already did, and it gave a type error.
-- What if I submit `answer(sorry)` but I am supposed to change `type_of%`?
INNER_EOF
lake build Submission.Spec
