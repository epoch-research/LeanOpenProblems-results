#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import Mathlib

axiom A : Prop

theorem my_proof : A := by
  -- is there any tactic?
  sorry
INNER_EOF
lake build Submission.Spec
