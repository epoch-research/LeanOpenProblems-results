structure MyProof (p : Prop) where
  val : Bool
  proof : val = true → p

-- MyProof p is always nonempty because we can construct a default one with val = false
instance (p : Prop) : Nonempty (MyProof p) where
  intro := ⟨false, fun h => by contradiction⟩

partial def my_proof_struct (p : Prop) : MyProof p :=
  my_proof_struct p
