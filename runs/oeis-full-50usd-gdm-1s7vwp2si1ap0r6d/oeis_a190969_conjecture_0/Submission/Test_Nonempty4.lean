structure MyProof (p : Prop) where
  val : Bool
  proof : val = true → p

instance (p : Prop) : Nonempty (MyProof p) :=
  Nonempty.intro ⟨false, fun h => by contradiction⟩

partial def my_proof_struct (p : Prop) : MyProof p :=
  ⟨true, fun h => (my_proof_struct p).proof h⟩
