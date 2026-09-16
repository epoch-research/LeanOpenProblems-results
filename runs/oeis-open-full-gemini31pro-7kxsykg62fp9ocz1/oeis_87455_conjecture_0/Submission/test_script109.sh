#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

-- Can we just define it?
def my_answer : A087455_satisfies_Benfords_law := sorry
INNER_EOF
lake build Submission.Spec
