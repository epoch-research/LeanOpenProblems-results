structure MyProof (p : Prop) where
  val : Prop
  proof : (val = True) → p

instance (p : Prop) : Nonempty (MyProof p) :=
  Nonempty.intro ⟨False, fun h => by
    have h_false : False := by
      rw [h] at * -- wait, if h has type False = True, we can get False by rewriting
      -- Actually, False = True is false, so we can use contradiction or nominal
      sorry
    exact h_false.elim⟩

partial def my_proof_struct (p : Prop) : MyProof p :=
  ⟨(my_proof_struct p).val, fun h => (my_proof_struct p).proof h⟩
