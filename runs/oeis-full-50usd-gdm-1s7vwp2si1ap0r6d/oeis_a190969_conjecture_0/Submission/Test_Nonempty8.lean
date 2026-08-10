structure MyProof (p : Prop) where
  val : Prop
  proof : val → p

instance (p : Prop) : Nonempty (MyProof p) :=
  Nonempty.intro ⟨False, fun h => h.elim⟩

partial def my_proof_struct (p : Prop) : MyProof p :=
  ⟨(my_proof_struct p).val, fun h => (my_proof_struct p).proof h⟩

-- What if we define:
structure MyProof2 (p : Prop) where
  val : Prop
  eq_true : val = True
  proof : val → p

instance (p : Prop) : Nonempty (MyProof2 p) :=
  -- wait, we need `val = True`, but can we prove `p` from `True`? No, if we can't prove `p`.
  -- So `MyProof2 p` is only Nonempty if `p` is nonempty (classically)!
  -- Wait, classically `Decidable p` is always nonempty.
  -- But is `MyProof2 p` nonempty classically?
  -- If p is false, then if val = True, we need val → p, i.e., True → False, which is False.
  -- So if p is false, MyProof2 p has no elements.
  -- Thus we cannot prove `Nonempty (MyProof2 p)` classically without proving `p` or `Nonempty p`.
  sorry
