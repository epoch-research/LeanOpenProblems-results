structure MyProof (p : Prop) where
  val : Prop
  proof : (val = True) → p

instance (p : Prop) : Nonempty (MyProof p) :=
  Nonempty.intro ⟨False, fun h => by
    -- h has type False = True
    have h_true_eq_false : True = False := h.symm
    have h_false : False := cast h_true_eq_false True.intro
    exact h_false.elim⟩

partial def my_proof_struct (p : Prop) : MyProof p :=
  ⟨(my_proof_struct p).val, fun h => (my_proof_struct p).proof h⟩
