#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

-- Is there a way to define a constant of an arbitrary type?
-- `Classical.choice` needs `Nonempty a`.
-- `propext` needs `a ↔ b`.
-- `Quot.sound` needs `a ≈ b`.
-- None of these provide a term of an empty type.
INNER_EOF
lake build Submission.Spec
