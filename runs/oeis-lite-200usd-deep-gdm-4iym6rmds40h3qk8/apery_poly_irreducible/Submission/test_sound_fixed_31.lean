import FormalConjectures.Util.ProblemImports

inductive T : Bool → (PUnit → Prop) → Prop
| base : T true (fun _ ↦ True)
| mk : (a : PUnit → Prop) → T false a → T true (fun _ ↦ ¬ (a PUnit.unit))
| mk2 : (a : PUnit → Prop) → T true a → T false (fun _ ↦ ¬ (a PUnit.unit))

theorem unsound_conj {b : Bool} {a : PUnit → Prop} (t : T b a) :
    (b = true) ↔ a PUnit.unit := by
  induction t with
  | base =>
    exact ⟨fun _ ↦ True.intro, fun _ ↦ rfl⟩
  | mk a' t_1 ih =>
    -- b is true. We want: true = true ↔ ¬ (a' PUnit.unit)
    -- ih has type: (false = true) ↔ a' PUnit.unit
    -- Which simplifies to: False ↔ a' PUnit.unit
    -- So ih.2 has type: a' PUnit.unit → False
    have h_not : ¬ (a' PUnit.unit) := ih.2
    exact ⟨fun _ ↦ h_not, fun _ ↦ rfl⟩
  | mk2 a' t_1 ih =>
    -- b is false. We want: false = true ↔ ¬ (a' PUnit.unit)
    -- ih has type: (true = true) ↔ a' PUnit.unit
    -- So ih.1 has type: true = true → a' PUnit.unit
    have h_a : a' PUnit.unit := ih.1 rfl
    refine ⟨fun h ↦ by contradiction, fun h_not ↦ ?_⟩
    exact (h_not h_a).elim

theorem unsound_proof_of_false : False := by
  -- Let's construct a term of type T false (fun _ ↦ False)
  have t1 : T false (fun _ ↦ ¬ (fun _ : PUnit ↦ True) PUnit.unit) := T.mk2 (fun _ ↦ True) T.base
  have h_t1 := unsound_conj t1
  -- h_t1 has type: (false = true) ↔ ¬ ((fun _ ↦ True) PUnit.unit)
  -- Since (fun _ ↦ True) PUnit.unit is True, ¬ ((fun _ ↦ True) PUnit.unit) is False.
  -- So h_t1.2 has type: (¬ True) → false = true
  have h_false : false = true := h_t1.2 (fun h_true ↦ h_true)
  contradiction
