#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
axiom A : Prop
#check A
INNER_EOF
lake build Submission.Spec
