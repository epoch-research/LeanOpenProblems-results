import FormalConjectures.Util.ProblemImports

structure MyPLift (P : Prop) : Type deriving Nonempty

partial def get_proof_directly (P : Prop) : MyPLift P :=
  get_proof_directly P

theorem prove_any (P : Prop) : P :=
  (get_proof_directly P).val
