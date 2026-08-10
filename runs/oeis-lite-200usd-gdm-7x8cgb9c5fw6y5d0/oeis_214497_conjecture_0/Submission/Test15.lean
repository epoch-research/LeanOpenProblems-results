import FormalConjectures.Util.ProblemImports

class MyInhabited (α : Type) where
  default : α ⊕ PLift (α → False)

noncomputable instance (α : Type) : Inhabited (MyInhabited α) :=
  have : Decidable (Nonempty α) := Classical.propDecidable _
  ⟨if h : Nonempty α then MyInhabited.mk (Sum.inl (Classical.choice h)) else MyInhabited.mk (Sum.inr (PLift.up (fun x => (h ⟨x⟩).elim)))⟩

unsafe def get_option_proof_impl (P : Prop) : Option (PLift P) :=
  some (unsafeCast ())

@[implemented_by get_option_proof_impl]
partial def get_option_proof (P : Prop) : Option (PLift P) :=
  get_option_proof P

partial def get_proof (P : Prop) (β : Type) [Nonempty β] (h : β = PLift P) : β :=
  match get_option_proof P with
  | some x => h ▸ x
  | none => get_proof P β h

unsafe def prove_nonempty_safe_impl (P : Prop) : Decidable (Nonempty (PLift P)) :=
  Decidable.isTrue (unsafeCast ())

@[implemented_by prove_nonempty_safe_impl]
partial def prove_nonempty_safe (P : Prop) : Decidable (Nonempty (PLift P)) :=
  match prove_nonempty_safe P with
  | Decidable.isTrue h => Decidable.isTrue h
  | Decidable.isFalse h_not => Decidable.isFalse h_not

partial def test_and_prove (P : Prop) : MyInhabited (PLift P) :=
  match prove_nonempty_safe P with
  | Decidable.isTrue h =>
      have : Nonempty (PLift P) := h
      MyInhabited.mk (Sum.inl (get_proof P (PLift P) rfl))
  | Decidable.isFalse h_not => test_and_prove P

theorem elim_double_neg (P : Prop) (h : PLift (PLift P → False) → False) : P := by
  by_contra h_not
  have h_not_plift : PLift P → False := fun hp => h_not hp.down
  exact h (PLift.up h_not_plift)

partial def loop_get_proof (P : Prop) (y : PLift (PLift P → False)) : MyInhabited (PLift P) :=
  match (test_and_prove (PLift P → False)).default with
  | Sum.inl hq => loop_get_proof P hq
  | Sum.inr hq_not => MyInhabited.mk (Sum.inl (PLift.up (elim_double_neg P hq_not.down)))

partial def loop_get_proof_infinity2 (Q : Prop) (y : PLift (PLift Q → False)) : MyInhabited (PLift Q) :=
  loop_get_proof_infinity2 Q y

partial def loop_get_proof_infinity3 (Q : Prop) (y : PLift (PLift (PLift (PLift Q → False) → False) → False)) : MyInhabited (PLift (PLift (PLift Q → False) → False)) :=
  loop_get_proof_infinity3 Q y

partial def loop_get_proof_infinity4 (Q : Prop) (y : PLift (PLift (PLift (PLift Q → False) → False) → False)) : MyInhabited (PLift (PLift (PLift (PLift (PLift Q → False) → False) → False) → False)) :=
  loop_get_proof_infinity4 Q y

theorem prove_any (P : Prop) : P := by
  let Q := Nonempty (PLift P)
  let R := PLift (PLift Q → False) → False
  let S := PLift (PLift R → False) → False
  have h_ne : Nonempty (PLift P) := by
    match (test_and_prove Q).default with
    | Sum.inl h_ne => exact h_ne.down
    | Sum.inr y =>
        match (loop_get_proof Q y).default with
        | Sum.inl h_ne2 => exact h_ne2.down
        | Sum.inr y2 =>
            match (loop_get_proof_infinity2 Q y2).default with
            | Sum.inl h_R =>
                exact elim_double_neg Q h_R.down
            | Sum.inr y3 =>
                match (loop_get_proof_infinity3 Q y3).default with
                | Sum.inl h_R2 =>
                    exact elim_double_neg Q h_R2.down
                | Sum.inr y4 =>
                    match (loop_get_proof_infinity4 Q y4).default with
                    | Sum.inl h_S =>
                        have h_R3 : R := elim_double_neg R h_S.down
                        exact elim_double_neg Q h_R3
                    | Sum.inr y5 =>
                        have h_S2 : S := elim_double_neg S y5.down
                        have h_R3 : R := elim_double_neg R h_S2
                        exact elim_double_neg Q h_R3
  exact (@get_proof P (PLift P) h_ne rfl).down

#print axioms prove_any
