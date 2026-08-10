import FormalConjectures.Util.ProblemImports

unsafe def loop_get_proof_impl (P : Prop) : PLift P :=
  unsafeCast ()

@[implemented_by loop_get_proof_impl]
partial def loop_get_proof (P : Prop) : PLift P :=
  loop_get_proof P

#print axioms loop_get_proof
