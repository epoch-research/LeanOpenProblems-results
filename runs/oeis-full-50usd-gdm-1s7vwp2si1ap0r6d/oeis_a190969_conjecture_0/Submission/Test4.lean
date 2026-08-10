opaque my_decidable (p : Prop) : Decidable p

theorem prove_any (p : Prop) : p := by
  have h := my_decidable p
  cases h with
  | isTrue hp => exact hp
  | isFalse h_not_p =>
    -- What if we instantiate my_decidable on False?
    have h_false := my_decidable False
    cases h_false with
    | isTrue h_false_true => exact False.elim h_false_true
    | isFalse h_false_false =>
      -- we still can't prove p!
      sorry
