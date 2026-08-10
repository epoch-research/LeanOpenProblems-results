structure Loeb (p : Prop) where
  val : Prop
  proof : (val → p) → p

instance (p : Prop) : Nonempty (Loeb p) :=
  Nonempty.intro ⟨True, fun f => f True.intro⟩

partial def my_proof_struct (p : Prop) : Loeb p :=
  ⟨(my_proof_struct p).val → p, fun f => (my_proof_struct p).proof f⟩
