macro_rules | `(type_of% $e) => `(False)

theorem test : ¬ (type_of% @id) := by
  intro h
  exact h
