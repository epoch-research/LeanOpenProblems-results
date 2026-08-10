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
    -- We want to prove T p.
    -- Since we have hq2 : T q, and we have hp2 : ∀ x, p x ↔ (x = True).
    -- And hq1 : ∀ x, q x ↔ (x = True).
    -- So p and q are both pointwise equivalent to `x = True`!
    -- So p and q are pointwise equivalent to each other!
    -- By propext, p x = q x for all x.
    -- By funext, p = q!
    -- So T p ↔ T q!
    -- Since T q is True, T p is True!
    have h_eq : p = q := by
      apply funext
      intro x
      apply propext
      constructor
      · intro hpx
        have h_true := (hp2 x).mp hpx
        rw [h_true] at hp2
        -- actually we can just do:
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
      · sorry
      · exact hp
    · sorry
