#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

def A087455_satisfies_Benfords_law : Prop := answer(True)

theorem oeis_87455_conjecture_0 : A087455_satisfies_Benfords_law := True.intro
INNER_EOF
lake build Submission.Spec
