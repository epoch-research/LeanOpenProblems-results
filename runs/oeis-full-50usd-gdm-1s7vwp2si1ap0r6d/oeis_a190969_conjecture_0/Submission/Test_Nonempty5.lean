structure MyProof (p : Prop) where
  val : Prop
  proof : val → p

instance (p : Prop) : Nonempty (MyProof p) :=
  Nonempty.intro ⟨False, fun h => h.elim⟩

partial def my_proof_struct (p : Prop) : MyProof p :=
  ⟨(my_proof_struct p).val, fun h => (my_proof_struct p).proof h⟩
