import FormalConjectures.Util.ProblemImports

unsafe def get_proof_of_impl (A : Prop) : PLift A :=
  unsafeCast ()

@[implemented_by get_proof_of_impl]
partial def get_proof_of (A : Prop) : PLift A :=
  get_proof_of A
