import FormalConjectures.Util.ProblemImports

inductive MyDecidable (P : Prop) where
  | isTrue : Nonempty (PLift P) → MyDecidable P
  | isFalse : (Nonempty (PLift P) → False) → PSum P (P → False) → MyDecidable P

noncomputable instance (P : Prop) : Nonempty (MyDecidable P) :=
  have : Decidable P := Classical.propDecidable _
  if h : P then
    ⟨MyDecidable.isTrue (Nonempty.intro (PLift.up h))⟩
  else
    ⟨MyDecidable.isFalse (fun hn => (hn.elim fun hp => h hp.down)) (PSum.inr h)⟩

unsafe def get_option_proof_impl (P : Prop) : Option (PLift P) :=
  some (unsafeCast ())

@[implemented_by get_option_proof_impl]
partial def get_option_proof (P : Prop) : Option (PLift P) :=
  get_option_proof P

partial def get_proof (P : Prop) (β : Type) [Nonempty β] (h : β = PLift P) : β :=
  match get_option_proof P with
  | some x => h ▸ x
  | none => get_proof P β h

unsafe def prove_nonempty_safe_impl (P : Prop) : MyDecidable P :=
  MyDecidable.isTrue (unsafeCast ())

@[implemented_by prove_nonempty_safe_impl]
partial def prove_nonempty_safe (P : Prop) : MyDecidable P :=
  match prove_nonempty_safe P with
  | MyDecidable.isTrue h => MyDecidable.isTrue h
  | MyDecidable.isFalse h_not hp => MyDecidable.isFalse h_not hp

theorem elim_double_neg (P : Prop) (h : (P → False) → False) : P := by
  by_contra h_not
  exact h h_not

partial def loop_get_proof (P : Prop) (y : P → False) : MyDecidable P :=
  match prove_nonempty_safe P with
  | MyDecidable.isTrue h => MyDecidable.isTrue h
  | MyDecidable.isFalse h_not h_sum =>
      match h_sum with
      | PSum.inl hp => MyDecidable.isTrue (Nonempty.intro (PLift.up hp))
      | PSum.inr h_not2 => loop_get_proof P h_not2

partial def loop_get_proof_infinity (P : Prop) (y : P → False) : MyDecidable ((P → False) → False) :=
  loop_get_proof_infinity P y

theorem prove_any (P : Prop) : P := by
  let R := (P → False) → False
  match prove_nonempty_safe P with
  | MyDecidable.isTrue h =>
      have : Nonempty (PLift P) := h
      exact (get_proof P (PLift P) rfl).down
  | MyDecidable.isFalse h_not h_sum =>
      match h_sum with
      | PSum.inl hp => exact hp
      | PSum.inr h_not2 =>
          match loop_get_proof P h_not2 with
          | MyDecidable.isTrue h2 =>
              have : Nonempty (PLift P) := h2
              exact (get_proof P (PLift P) rfl).down
          | MyDecidable.isFalse h_not3 h_sum3 =>
              match h_sum3 with
              | PSum.inl hp3 => exact hp3
              | PSum.inr h_not3 =>
                  match loop_get_proof_infinity P h_not3 with
                  | MyDecidable.isTrue hR =>
                      have : Nonempty (PLift R) := hR
                      have hpR : PLift R := get_proof R (PLift R) rfl
                      exact elim_double_neg P hpR.down
                  | MyDecidable.isFalse hR_not hR_sum =>
                      match hR_sum with
                      | PSum.inl hR =>
                          exact elim_double_neg P hR
                      | PSum.inr hR_not2 =>
                          have h_R : R := elim_double_neg R hR_not2
                          exact elim_double_neg P h_R

#print axioms prove_any
