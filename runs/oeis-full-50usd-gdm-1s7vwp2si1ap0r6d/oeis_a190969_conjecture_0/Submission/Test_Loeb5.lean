structure Loeb (p : Prop) where
  val : Prop
  proof : (val → p) → p

instance (p : Prop) : Nonempty (Loeb p) :=
  Nonempty.intro ⟨True, fun f => f True.intro⟩

partial def my_proof_struct (p : Prop) : Loeb p :=
  ⟨(my_proof_struct p).val, fun f => (my_proof_struct p).proof f⟩

partial def my_proof_fn (P : Prop) (h : (my_proof_struct P).val) : P :=
  (my_proof_struct P).proof (my_proof_fn P)
