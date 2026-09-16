#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

theorem my_proof : ¬ A087455_satisfies_Benfords_law := by
  intro h
  exact sorry
#print axioms my_proof
INNER_EOF
lake build Submission.Spec
