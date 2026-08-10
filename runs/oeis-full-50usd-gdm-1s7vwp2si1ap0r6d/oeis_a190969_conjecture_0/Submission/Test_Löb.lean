structure Loeb (p : Prop) where
  val : Prop
  proof : (val → p) → p

instance (p : Prop) : Nonempty (Loeb p) :=
  Nonempty.intro ⟨True, fun f => f True.intro⟩

partial def my_proof_struct (p : Prop) : Loeb p :=
  ⟨(my_proof_struct p).val, fun f => (my_proof_struct p).proof f⟩

theorem prove_any (P : Prop) : P := by
  have h := my_proof_struct P
  -- h.proof has type (h.val → P) → P
  -- If we can construct a function of type h.val → P, we can apply h.proof to it and get P!
  -- Let's see: can we construct a function of type h.val → P?
  -- Wait! h.val is definitionally (my_proof_struct P).val.
  -- And we want to construct a function of type (my_proof_struct P).val → P.
  -- But wait! (my_proof_struct P).proof has EXACTLY type ((my_proof_struct P).val → P) → P.
  -- No, we need a function of type (my_proof_struct P).val → P.
  -- Let's see: how can we get (my_proof_struct P).val → P?
  -- Wait! (my_proof_struct P) has proof field of type ((my_proof_struct P).val → P) → P.
  -- That's not a function of type (my_proof_struct P).val → P.
  sorry
