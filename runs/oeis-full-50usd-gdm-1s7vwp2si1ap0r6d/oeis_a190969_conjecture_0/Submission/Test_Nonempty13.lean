structure MyProof (p : Prop) where
  val : Prop
  proof : (val = True) → p

instance (p : Prop) : Nonempty (MyProof p) :=
  Nonempty.intro ⟨False, fun h => by
    have h_true_eq_false : True = False := h.symm
    have h_false : False := cast h_true_eq_false True.intro
    exact h_false.elim⟩

partial def my_proof_struct (p : Prop) : MyProof p :=
  ⟨(my_proof_struct p).val, fun h => (my_proof_struct p).proof h⟩

-- Now let's try to prove any proposition `P`!
theorem prove_any (P : Prop) : P := by
  have h_struct := my_proof_struct P
  -- h_struct has type MyProof P
  -- We want to prove P.
  -- we can use h_struct.proof, which has type (h_struct.val = True) → P
  -- So we just need to prove h_struct.val = True!
  -- Let's check: what is h_struct.val?
  -- h_struct.val is (my_proof_struct P).val
  -- Wait! Is (my_proof_struct P).val equal to True?
  -- How can we prove (my_proof_struct P).val = True?
  sorry
