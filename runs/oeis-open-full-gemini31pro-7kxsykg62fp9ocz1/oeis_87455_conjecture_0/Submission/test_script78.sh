#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

open LinearRecurrence

axiom A087455_satisfies_Benfords_law : Prop

theorem oeis_87455_conjecture_0 : A087455_satisfies_Benfords_law := answer(True)
INNER_EOF
lake build Submission.Spec
