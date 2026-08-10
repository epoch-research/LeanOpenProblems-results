inductive T : Bool → (PUnit → Prop) → Prop
| base : T true (fun _ ↦ False)
| mk : (a : PUnit → Prop) → T false a → T true (fun _ ↦ ¬ (a PUnit.unit))
| mk2 : (a : PUnit → Prop) → T true a → T false (fun _ ↦ ¬ (a PUnit.unit))

theorem get_eq_for_true {a} (t : T true a) : a = (fun _ ↦ False) := by
  induction t with
  | base => rfl
  | mk a' t_1 ih =>
    -- goal: (fun _ ↦ ¬ a' PUnit.unit) = (fun _ ↦ False)
    -- wait, we have ih : a' = (fun _ ↦ False) ?
    -- No, ih is for t_1 : T false a'.
    -- So ih has type: a' = (fun _ ↦ False) ?
    -- No, ih is the induction hypothesis for t_1.
    -- Since t_1 has index `false`, what is the type of ih?
    -- Let's check!
    sorry
