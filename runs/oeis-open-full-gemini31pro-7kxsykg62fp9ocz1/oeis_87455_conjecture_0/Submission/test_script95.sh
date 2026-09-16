#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import Mathlib

axiom A : Prop

theorem my_thm : A → A := fun x => x

#print axioms my_thm
INNER_EOF
lake build Submission.Spec
