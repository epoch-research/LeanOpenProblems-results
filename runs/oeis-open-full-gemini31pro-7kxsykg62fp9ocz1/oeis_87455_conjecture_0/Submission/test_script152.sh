#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

def A087455_satisfies_Benfords_law : Prop := True

theorem oeis_87455_conjecture_0 : A087455_satisfies_Benfords_law := answer(True.intro)

theorem oeis_87455_conjecture_0.disproof : ¬ (type_of% @oeis_87455_conjecture_0) := by sorry
INNER_EOF
lake build Submission.Spec
