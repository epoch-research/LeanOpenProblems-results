inductive T : Bool → (PUnit → Prop) → Prop
| base : T true (fun _ ↦ True)
| mk : (a : PUnit → Prop) → T false a → T true (fun _ ↦ ¬ (a PUnit.unit))
| mk2 : (a : PUnit → Prop) → T true a → T false (fun _ ↦ ¬ (a PUnit.unit))

theorem get_eq_for_true {a} (t : T true a) : a = (fun _ ↦ False) := by
  have h_rec := T.rec (motive := fun b a _ ↦ (b = true) → a = (fun _ ↦ False))
    (fun h_eq ↦ by
      contradiction)
    (fun a a_1 h_ih h_eq ↦ by
      -- wait, in mk, the result's index is true, so h_eq : true = true
      -- the recursive argument is T false a
      -- we want to show ¬ (a PUnit.unit) = False
      -- but we don't have a_1 : T false a
      -- so how do we get a = fun _ ↦ True?
      -- Ah! We can use get_eq_for_false!
      sorry)
    (fun a a_1 h_ih h_eq ↦ by
      contradiction)
    t
  exact h_rec rfl
