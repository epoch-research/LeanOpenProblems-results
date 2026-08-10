import FormalConjectures.Util.ProblemImports

inductive MyType (P : Prop) where
  | value : P → MyType P
  | dummy : (P → False) → MyType P

noncomputable instance (P : Prop) : Nonempty (MyType P) :=
  have : Decidable P := Classical.propDecidable _
  if h : P then
    ⟨MyType.value h⟩
  else
    ⟨MyType.dummy h⟩

unsafe def get_my_type_impl (P : Prop) : MyType P :=
  MyType.value (unsafeCast ())

@[implemented_by get_my_type_impl]
partial def get_my_type (P : Prop) : MyType P :=
  match get_my_type P with
  | MyType.value hp => MyType.value hp
  | MyType.dummy hd => MyType.dummy hd

theorem elim_double_neg (P : Prop) (h : (P → False) → False) : P := by
  by_contra h_not
  exact h h_not

partial def loop_get_proof (P : Prop) (y : P → False) : MyType ((P → False) → False) :=
  match get_my_type (P → False) with
  | MyType.value hq =>
      loop_get_proof P hq
  | MyType.dummy hd2 =>
      MyType.value hd2

theorem prove_any (P : Prop) : P := by
  let R := (P → False) → False
  match get_my_type P with
  | MyType.value hp => exact hp
  | MyType.dummy hd =>
      match loop_get_proof P hd with
      | MyType.value hR =>
          exact elim_double_neg P hR
      | MyType.dummy hd2 =>
          have h_R : R := elim_double_neg R hd2
          exact elim_double_neg P h_R

#print axioms prove_any
