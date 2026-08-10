theorem subtype_eq_cases {α : Type} (p : α → Prop) (p_choose : α → Prop) (h_spec : Subtype p = Subtype p_choose) (x : Subtype p) :
    (match cast h_spec x with | ⟨val, _⟩ => val) = x.val := by
  cases h_spec
  rfl
