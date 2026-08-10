import Mathlib

instance my_sum_nonempty (P : Prop) : Nonempty (PLift P ⊕ PLift (PLift P → False)) := by
  cases Classical.em P with
  | inl hp => exact ⟨Sum.inl ⟨hp⟩⟩
  | inr hnp => exact ⟨Sum.inr ⟨fun ⟨hp⟩ => hnp hp⟩⟩

partial def get_sum (P : Prop) : PLift P ⊕ PLift (PLift P → False) :=
  get_sum P

partial def prove_P (P : Prop) (s : PLift P ⊕ PLift (PLift P → False)) : PLift P ⊕ PLift (PLift P → False) :=
  match s with
  | Sum.inl hp => Sum.inl hp
  | Sum.inr hnp =>
    match prove_P (PLift P → False) (get_sum (PLift P → False)) with
    | Sum.inl hnnp => Sum.inr hnnp
    | Sum.inr hnnnp => False.elim (hnnnp.down hnp)

#print axioms prove_P
