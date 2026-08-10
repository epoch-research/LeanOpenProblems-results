open Classical

inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

theorem T_subtype_eq_inj (t1 t2 : T) (h : { y : T // y = t1 } = { y : T // y = t2 }) : t1 = t2 := by
  let val1 : { y : T // y = t1 } := ⟨t1, rfl⟩
  let val2 : { y : T // y = t2 } := cast h val1
  have h_eq : val2.val = val1.val := by
    -- let's try some tactics!
    sorry
  have h_val1 : val1.val = t1 := rfl
  rw [h_val1] at h_eq
  have h_prop := val2.property
  rw [h_eq] at h_prop
  rw [← h_prop]
