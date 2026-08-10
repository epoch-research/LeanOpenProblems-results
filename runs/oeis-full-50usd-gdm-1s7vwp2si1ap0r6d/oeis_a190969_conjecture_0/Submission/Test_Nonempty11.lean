structure MyProof (p : Prop) where
  val : Prop
  proof : (val = True) → p

instance (p : Prop) : Nonempty (MyProof p) :=
  Nonempty.intro ⟨False, fun h => by
    -- h has type False = True
    -- We want to prove p
    -- Can we rewrite False = True to get False?
    have h_false : False := by
      -- we want to prove False
      -- if we rewrite using h: False = True (from right to left), we can change the goal from False to True!
      rw [← h]
      trivial
    exact h_false.elim⟩

partial def my_proof_struct (p : Prop) : MyProof p :=
  ⟨(my_proof_struct p).val, fun h => (my_proof_struct p).proof h⟩
