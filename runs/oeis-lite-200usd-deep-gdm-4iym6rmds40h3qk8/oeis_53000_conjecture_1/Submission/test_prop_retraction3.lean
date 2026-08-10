def sb := (Prop → Prop) → Prop

open Classical

noncomputable def inj (T : sb) : Prop :=
  ∃ (p : Prop → Prop), (∀ x, p x ↔ (x = True)) ∧ T p

noncomputable def proj (P : Prop) : sb :=
  fun p => P ∧ (∀ x, p x ↔ (x = True))

theorem proj_inj (T : sb) : proj (inj T) = T := by
  apply funext
  intro p
  dsimp [proj, inj]
  constructor
  · intro h
    obtain ⟨hp1, hp2⟩ := h
    obtain ⟨q, hq1, hq2⟩ := hp1
    have h_eq : p = q := by
      apply funext
      intro x
      apply propext
      constructor
      · intro hpx
        have h_true := (hp2 x).mp hpx
        have h_qx := (hq1 x).mpr h_true
        exact h_qx
      · intro hqx
        have h_true := (hq1 x).mp hqx
        have h_px := (hp2 x).mpr h_true
        exact h_px
    rw [h_eq]
    exact hq2
  · intro hp
    constructor
    · use p
      constructor
      · intro x
        constructor
        · intro hpx
          -- Wait, we need p x ↔ (x = True).
          -- But wait! T is a predicate on Prop → Prop.
          -- Does p satisfy ∀ x, p x ↔ (x = True)?
          -- Not necessarily! T can be applied to any p.
          -- Ah!!!
          -- If p does not satisfy this, then proj (inj T) is NOT equal to T!
          -- Yes, because proj (inj T) only returns True for p that satisfy the True-equivalence!
          -- So they are only equal on the subset of Prop → Prop that are equivalent to `x = True`.
          -- So this is not a retraction on the whole of sb!
          sorry
      · exact hp
    · sorry
