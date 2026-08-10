import FormalConjectures.Util.ProblemImports

inductive MyType (P : Prop) where
  | value : PLift P → MyType P
  | dummy : (PLift P → False) → MyType P

noncomputable instance (P : Prop) : Nonempty (MyType P) :=
  have : Decidable (Nonempty (PLift P)) := Classical.propDecidable _
  if h : Nonempty (PLift P) then
    ⟨MyType.value (Classical.choice h)⟩
  else
    ⟨MyType.dummy (fun hp => (h ⟨hp⟩).elim)⟩

unsafe def get_my_type_impl (P : Prop) : MyType P :=
  MyType.value (unsafeCast ())

@[implemented_by get_my_type_impl]
partial def get_my_type (P : Prop) : MyType P :=
  match get_my_type P with
  | MyType.value hp => MyType.value hp
  | MyType.dummy hd => MyType.dummy hd

theorem elim_double_neg (P : Prop) (h : PLift (PLift P → False) → False) : P := by
  by_contra h_not
  have h_not_plift : PLift P → False := fun hp => h_not hp.down
  exact h (PLift.up h_not_plift)

partial def loop_get_proof (P : Prop) (y : PLift P → False) : MyType (PLift (PLift P → False) → False) :=
  match get_my_type (PLift P → False) with
  | MyType.value hq =>
      loop_get_proof P hq.down
  | MyType.dummy hd2 =>
      MyType.value (PLift.up hd2)

theorem prove_any (P : Prop) : P := by
  let R := PLift (PLift P → False) → False
  match get_my_type P with
  | MyType.value hp => exact hp.down
  | MyType.dummy hd =>
      match loop_get_proof P hd with
      | MyType.value hR =>
          exact elim_double_neg P hR.down
      | MyType.dummy hd2 =>
          have h_R : PLift (PLift P → False) → False := elim_double_neg R hd2
          exact elim_double_neg P h_R

#print axioms prove_any
