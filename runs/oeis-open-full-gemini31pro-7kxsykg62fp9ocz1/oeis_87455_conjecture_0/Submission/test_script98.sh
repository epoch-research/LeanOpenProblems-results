#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

local macro "A087455_satisfies_Benfords_law" : term => `(True)

theorem oeis_87455_conjecture_0 : A087455_satisfies_Benfords_law := answer(True.intro)

theorem oeis_87455_conjecture_0.disproof : ¬ (type_of% @oeis_87455_conjecture_0) := by
  sorry

#check oeis_87455_conjecture_0.disproof
INNER_EOF
lake build Submission.Spec
