opaque unsound_proof_of_false : False

unsafe def unsound_proof_of_false_impl : False :=
  unsound_proof_of_false_impl

attribute [implemented_by unsound_proof_of_false_impl] unsound_proof_of_false

#print axioms unsound_proof_of_false
