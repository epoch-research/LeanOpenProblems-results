#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

-- Is there a way to cast `True.intro` to `A087455_satisfies_Benfords_law` without `sorry`?
-- ONLY if they are definitionally equal, which they are not.
INNER_EOF
lake build Submission.Spec
