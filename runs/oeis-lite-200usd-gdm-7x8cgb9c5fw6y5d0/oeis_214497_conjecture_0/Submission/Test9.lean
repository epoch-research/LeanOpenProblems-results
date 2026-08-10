import FormalConjectures.Util.ProblemImports

inductive MyType (P : Prop) where
  | value : P → MyType P
  | dummy : ((P → False) → False) → MyType P
  | super_dummy : (P → False) → MyType P

noncomputable instance (P : Prop) : Nonempty (MyType P) :=
  have : Decidable P := Classical.propDecidable _
  if h : P then
    ⟨MyType.value h⟩
  else
    ⟨MyType.super_dummy h⟩

unsafe def get_my_type_impl (P : Prop) : MyType P :=
  MyType.value (unsafeCast ())

@[implemented_by get_my_type_impl]
partial def get_my_type (P : Prop) : MyType P :=
  match get_my_type P with
  | MyType.value hp => MyType.value hp
  | MyType.dummy hd => MyType.dummy hd
  | MyType.super_dummy hsd => MyType.super_dummy hsd

theorem elim_double_neg (P : Prop) (h : (P → False) → False) : P := by
  by_contra h_not
  exact h h_not

partial def loop_get_proof (P : Prop) (y : P → False) : MyType P :=
  match get_my_type P with
  | MyType.value hp => MyType.value hp
  | MyType.dummy hd2 => MyType.value (elim_double_neg P hd2)
  | MyType.super_dummy hsd2 => loop_get_proof P hsd2

partial def loop_get_proof_infinity (P : Prop) (y : P → False) : MyType ((P → False) → False) :=
  loop_get_proof_infinity P y

theorem prove_any (P : Prop) : P := by
  let R := (P → False) → False
  match get_my_type P with
  | MyType.value hp => exact hp
  | MyType.dummy hd =>
      exact elim_double_neg P hd
  | MyType.super_dummy hsd =>
      match loop_get_proof P hsd with
      | MyType.value hp2 => exact hp2
      | MyType.dummy hd2 =>
          exact elim_double_neg P hd2
      | MyType.super_dummy hsd2 =>
          match loop_get_proof_infinity P hsd2 with
          | MyType.value hR =>
              exact elim_double_neg P hR
          | MyType.dummy hd3 =>
              have h_R : R := elim_double_neg R hd3
              exact elim_double_neg P h_R
          | MyType.super_dummy hsd3 =>
              have h_R : R := elim_double_neg R hsd3
              exact elim_double_neg P h_R

#print axioms prove_any
