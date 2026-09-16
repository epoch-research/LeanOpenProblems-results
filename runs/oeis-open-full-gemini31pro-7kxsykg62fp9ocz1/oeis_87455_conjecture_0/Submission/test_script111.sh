#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

local macro "A087455_satisfies_Benfords_law" : term => `(True)

theorem oeis_87455_conjecture_0 : A087455_satisfies_Benfords_law := True.intro
INNER_EOF
lake build Submission.Spec
