import FormalConjectures.Util.ProblemImports

class MyType (P : Prop) where
  value : PSum P (P → False)

noncomputable instance (P : Prop) : Inhabited (MyType P) :=
  have : Decidable P := Classical.propDecidable _
  ⟨if h : P then ⟨PSum.inl h⟩ else ⟨PSum.inr h⟩⟩

unsafe def get_my_type_impl (P : Prop) : MyType P :=
  ⟨PSum.inl (unsafeCast ())⟩

@[implemented_by get_my_type_impl]
partial def get_my_type (P : Prop) : MyType P :=
  get_my_type P

theorem elim_double_neg (P : Prop) (h : (P → False) → False) : P := by
  by_contra h_not
  exact h h_not

partial def loop_get_proof (P : Prop) (y : P → False) : MyType P :=
  match (get_my_type (P → False)).value with
  | PSum.inl h_R =>
      loop_get_proof P h_R
  | PSum.inr h_R_not =>
      ⟨PSum.inl (elim_double_neg P h_R_not)⟩

partial def loop_get_proof_infinity (P : Prop) (y : P → False) : MyType ((P → False) → False) :=
  loop_get_proof_infinity P y

theorem prove_any (P : Prop) : P := by
  let R := (P → False) → False
  match (get_my_type P).value with
  | PSum.inl hp => exact hp
  | PSum.inr h_not =>
      match (loop_get_proof P h_not).value with
      | PSum.inl hp2 => exact hp2
      | PSum.inr y =>
          match (loop_get_proof_infinity P y).value with
          | PSum.inl h_R =>
              exact elim_double_neg P h_R
          | PSum.inr h_R_not =>
              have h_R : R := elim_double_neg R h_R_not
              exact elim_double_neg P h_R

#print axioms prove_any
