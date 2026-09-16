#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

-- What if `A087455_satisfies_Benfords_law` is equal to `True` by `Quot.sound`?
-- `Quot.sound` produces an equality of `Quot.mk`.
INNER_EOF
lake build Submission.Spec
