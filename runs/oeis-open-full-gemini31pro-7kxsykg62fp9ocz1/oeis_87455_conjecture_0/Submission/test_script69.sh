#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import Mathlib

axiom A : Prop

theorem foo : A := sorry

theorem foo.disproof : ¬ (type_of% @foo) := sorry
INNER_EOF
lake build Submission.Spec
