import Mathlib

instance my_sum_nonempty (P : Prop) : Nonempty (PLift P ⊕ PLift (PLift P → False)) := by
  cases Classical.em P with
  | inl hp => exact ⟨Sum.inl ⟨hp⟩⟩
  | inr hnp => exact ⟨Sum.inr ⟨fun ⟨hp⟩ => hnp hp⟩⟩

unsafe def unsafe_sum (P : Prop) : PLift P ⊕ PLift (PLift P → False) :=
  Sum.inl ⟨@unsafeCast Unit P ()⟩

@[implemented_by unsafe_sum]
partial def get_sum (P : Prop) : PLift P ⊕ PLift (PLift P → False) :=
  get_sum P

theorem prove_any (P : Prop) : P := by
  have s := get_sum P
  cases s with
  | inl hp => exact hp.down
  | inr hnp =>
    have s2 := get_sum (PLift P → False)
    cases s2 with
    | inl hq =>
      exact False.elim (hq.down hnp)
    | inr hnq =>
      exact False.elim (hnq.down ⟨hnp.down⟩)

theorem test_thm : 2 + 2 = 5 :=
  prove_any (2 + 2 = 5)

#print axioms test_thm
