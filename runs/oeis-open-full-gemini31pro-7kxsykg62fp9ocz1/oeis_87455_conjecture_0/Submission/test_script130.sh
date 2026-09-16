#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

axiom A087455_satisfies_Benfords_law : Prop

-- Can we prove `A087455_satisfies_Benfords_law` by defining an instance?
class MyClass (p : Prop) where
  val : p

-- No, we cannot construct a term of an empty type, even with classes.
INNER_EOF
lake build Submission.Spec
