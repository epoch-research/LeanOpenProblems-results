import FormalConjectures.Util.ProblemImports

theorem prop_subtype_eq_inj (P1 P2 : Prop) (h : { y : Prop // y = P1 } = { y : Prop // y = P2 }) : P1 ↔ P2 := by
  constructor
  · intro hP1
    let val1 : { y : Prop // y = P1 } := ⟨P1, rfl⟩
    let val2 : { y : Prop // y = P2 } := cast h val1
    have h_heq : HEq val2 val1 := cast_heq h val1
    have h_coe_heq : HEq val2.val val1.val := by
      -- we can use Subtype.heq_iff_coe_heq
      have h_eq_types : Prop = Prop := rfl
      have h_eq_preds : (fun y : Prop => y = P2) ≍ (fun y : Prop => y = P1) := by
        -- wait, how to prove predicate HEq?
        -- since they both have type Prop → Prop, HEq is Eq!
        -- and they are equal because the types { y // y = P1 } and { y // y = P2 } are equal?
        -- Actually, if we do cases on h, then the predicates become equal!
        sorry
      exact (Subtype.heq_iff_coe_heq h_eq_types h_eq_preds).mp h_heq
    have h_eq : val2.val = val1.val := eq_of_heq h_coe_heq
    have h_val1 : val1.val = P1 := rfl
    rw [h_val1] at h_eq
    have h_prop := val2.property
    rw [h_eq] at h_prop
    rw [← h_prop]
    exact hP1
  · sorry
