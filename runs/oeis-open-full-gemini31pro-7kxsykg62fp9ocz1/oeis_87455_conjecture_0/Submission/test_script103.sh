#!/bin/bash
cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports

open LinearRecurrence

def A087455 (n : ℕ) : ℤ :=
  let order : ℕ := 2
  let coeffs : Fin order → ℤ := fun i => Fin.cases (-3) 2 i
  let E : LinearRecurrence ℤ := ⟨order, coeffs⟩
  let init : Fin order → ℤ := fun i => Fin.cases 1 1 i
  E.mkSol init n

def A087455_satisfies_Benfords_law : Prop := False

theorem oeis_87455_conjecture_0 : A087455_satisfies_Benfords_law := by
  sorry

theorem oeis_87455_conjecture_0.disproof : ¬ (type_of% @oeis_87455_conjecture_0) := id
INNER_EOF
lake build Submission.Spec
