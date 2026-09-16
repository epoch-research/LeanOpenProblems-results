#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

theorem my_thm : A087455_satisfies_Benfords_law := by
  have h : A087455_satisfies_Benfords_law ↔ True := sorry
  -- ...
  sorry
INNER_EOF
lake build Submission.Spec
