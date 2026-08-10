import FormalConjectures.Util.ProblemImports

inductive MyType (P : Prop) : Type where
  | inl : Inhabited P → MyType P
  | inr : (Inhabited P → False) → MyType P

theorem mytype_nonempty (P : Prop) : Nonempty (MyType P) := by
  cases Classical.em (Nonempty (Inhabited P)) with
  | inl h =>
    have inst := Classical.choice h
    exact ⟨MyType.inl inst⟩
  | inr h =>
    have h_not : Inhabited P → False := fun hp => h ⟨hp⟩
    exact ⟨MyType.inr h_not⟩

instance (P : Prop) : Nonempty (MyType P) :=
  mytype_nonempty P

unsafe def unsafe_dec (P : Prop) : MyType P :=
  MyType.inl ⟨@unsafeCast Unit P ()⟩

@[implemented_by unsafe_dec]
partial def safe_dec (P : Prop) : MyType P :=
  safe_dec P

theorem prove_any (P : Prop) : P := by
  have d0 := safe_dec P
  cases d0 with
  | inl h0 =>
    exact h0.default
  | inr h0 =>
    have d1 := safe_dec (Inhabited P → False)
    cases d1 with
    | inr h2 =>
      exact False.elim (h2 ⟨h0⟩)
    | inl h1 =>
      have d2 := safe_dec (Inhabited (Inhabited P → False) → False)
      cases d2 with
      | inr h4 =>
        exact False.elim (h4 ⟨h1⟩)
      | inl h3 =>
        exact False.elim ((h3.default) h1)

theorem test_thm : 2 + 2 = 5 :=
  prove_any (2 + 2 = 5)

#print axioms test_thm






