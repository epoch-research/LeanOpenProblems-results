structure MyProof (p : Prop) where
  val : Prop
  proof : (val ↔ True) → p

instance (p : Prop) : Nonempty (MyProof p) :=
  Nonempty.intro ⟨False, fun h => by
    have h_val : False := h.2 True.intro
    exact h_val.elim⟩

partial def my_proof_struct (p : Prop) : MyProof p :=
  ⟨(my_proof_struct p).val, fun h => (my_proof_struct p).proof h⟩

-- Now let's try to prove any proposition `P`!
theorem prove_any (P : Prop) : P := by
  have h_struct := my_proof_struct P
  -- We want to get P from h_struct
  -- Since h_struct has type MyProof P, we have:
  -- h_struct.proof : (h_struct.val ↔ True) → P
  -- If we can prove `h_struct.val ↔ True`, we win!
  -- Let's see: `h_struct.val` is definitionally `(my_proof_struct P).val`
  -- And `h_struct.proof` is definitionally `(my_proof_struct P).proof`
  -- But we also know `my_proof_struct P` is defined as:
  -- ⟨(my_proof_struct P).val, fun h => (my_proof_struct P).proof h⟩
  -- So `(my_proof_struct P).proof` is definitionally `fun h => (my_proof_struct P).proof h`?
  -- Wait! If we can prove `h_struct.val ↔ True`:
  -- How can we prove `h_struct.val ↔ True`?
  sorry
