structure MyProof (p : Prop) where
  val : Prop
  proof : val → p

instance (p : Prop) : Nonempty (MyProof p) :=
  Nonempty.intro ⟨False, fun h => h.elim⟩

partial def my_proof_struct (p : Prop) : MyProof p :=
  ⟨(my_proof_struct p).val, fun h => (my_proof_struct p).proof h⟩

-- Can we prove that `(my_proof_struct p).val` is `True`?
-- Let's check:
-- What is the definitional equality of (my_proof_struct p).val?
-- Defeq: (my_proof_struct p).val = (my_proof_struct p).val. That doesn't reduce!
-- Wait, what if we define my_proof_struct with a parameter or another way?
EOF
