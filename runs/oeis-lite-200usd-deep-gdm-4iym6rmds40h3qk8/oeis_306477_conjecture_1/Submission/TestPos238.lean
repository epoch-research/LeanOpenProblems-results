def Set (X : Type) : Type := X → Prop

theorem hurkens_paradox_prop {U : Prop} (inj : ((U → Prop) → Prop) → U) (proj : U → (U → Prop) → Prop)
    (proj_inj : ∀ F, proj (inj F) = F) : False := by
  let τ (S : (U → Prop) → Prop) : U := inj S
  let σ (S : U) : (U → Prop) → Prop := proj S
  have στ : ∀ {s S}, σ (τ S) s ↔ S s := fun {s S} => by
    have h := proj_inj S
    dsimp [σ, τ]
    rw [h]
  let ω : (U → Prop) → Prop := fun p => ∀ x, σ x p → p x
  let δ (S : (U → Prop) → Prop) := ∀ p, S p → p (τ S)
  have h_delta_omega : δ ω := fun p hp => hp (τ ω) (στ.mpr hp)
  let p0 : U → Prop := fun y => ¬ δ (σ y)
  have h_omega_p0 : ω p0 := by
    intro x hx h_delta
    have h_not : p0 (τ (σ x)) := h_delta p0 hx
    have h_eq : σ (τ (σ x)) = σ x := by
      funext y
      apply propext
      exact στ
    change ¬ δ (σ (τ (σ x))) at h_not
    rw [h_eq] at h_not
    exact h_not h_delta
  have h_not_delta_omega : ¬ δ ω := by
    have h_not : p0 (τ ω) := h_omega_p0 (τ ω) (by
      rw [στ]
    )
    have h_eq : σ (τ ω) = ω := by
      funext y
      apply propext
      exact στ
    change ¬ δ (σ (τ ω)) at h_not
    rw [h_eq] at h_not
    exact h_not
  exact h_not_delta_omega h_delta_omega
