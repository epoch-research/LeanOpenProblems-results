#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

set_option google.answer "with_auxiliary"

theorem oeis_87455_conjecture_0 : A087455_satisfies_Benfords_law := answer(sorry)

#print axioms oeis_87455_conjecture_0
INNER_EOF
lake build Submission.Spec
