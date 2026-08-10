open Classical

theorem prop_subtype_eq_inj (P1 P2 : Prop) (h : { y : Prop // y = P1 } = { y : Prop // y = P2 }) : P1 ↔ P2 := by
  constructor
  · intro hP1
    let val1 : { y : Prop // y = P1 } := ⟨P1, rfl⟩
    let val2 : { y : Prop // y = P2 } := cast h val1
    have h_heq : HEq val2 val1 := cast_heq h val1
    -- val2.val has type Prop, val1.val has type Prop.
    -- Since they both have type Prop, their HEq is Eq!
    have h_eq : val2.val = val1.val := eq_of_heq h_heq
    -- val1.val is P1.
    have h_val1 : val1.val = P1 := rfl
    rw [h_val1] at h_eq
    -- val2.property has type: val2.val = P2
    have h_prop := val2.property
    rw [h_eq] at h_prop
    -- h_prop has type: P1 = P2
    -- Since P1 is true, and P1 = P2, we get P2!
    rw [← h_prop]
    exact hP1
  · intro hP2
    let val1 : { y : Prop // y = P2 } := ⟨P2, rfl⟩
    let val2 : { y : Prop // y = P1 } := cast h.symm val1
    have h_heq : HEq val2 val1 := cast_heq h.symm val1
    have h_eq : val2.val = val1.val := eq_of_heq h_heq
    have h_val1 : val1.val = P2 := rfl
    rw [h_val1] at h_eq
    have h_prop := val2.property
    rw [h_eq] at h_prop
    rw [← h_prop]
    exact hP2
