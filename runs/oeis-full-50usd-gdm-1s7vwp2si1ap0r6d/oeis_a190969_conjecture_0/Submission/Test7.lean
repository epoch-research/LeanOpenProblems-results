structure MyProof (p : Prop) where
  proof : p

partial def my_proof_struct (p : Prop) : MyProof p where
  proof := (my_proof_struct p).proof
