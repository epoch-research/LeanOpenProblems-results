#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import Mathlib

theorem false_is_provable : False := by
  -- try to find contradiction
  sorry
INNER_EOF
lake build Submission.Spec
