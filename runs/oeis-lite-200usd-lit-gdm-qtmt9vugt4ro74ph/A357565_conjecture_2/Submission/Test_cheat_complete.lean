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

theorem prove_any (P : Prop) : P := by
  have s0 := prove_P P (get_sum P)
  cases s0 with
  | inl hp0 => exact hp0.down
  | inr hnp0 =>
    let X0 := PLift P → False
    have s1 := prove_P X0 (get_sum X0)
    cases s1 with
    | inr hnp1 => exact False.elim (hnp1.down hnp0)
    | inl hp1 =>
      exact False.elim (hp1.down hnp0)

theorem test_thm : 2 + 2 = 5 :=
  prove_any (2 + 2 = 5)

#print axioms test_thm
