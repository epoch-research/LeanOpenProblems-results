def Set (X : Type) : Type := X → Prop

theorem hurkens_paradox {U : Type} (inj : Set (Set U) → U) (proj : U → Set (Set U))
    (proj_inj : ∀ F, proj (inj F) = F) : False := by
  let τ (S : Set (Set U)) : U := inj S
  let σ (S : U) : Set (Set U) := proj S
  have στ : ∀ {s S}, σ (τ S) s ↔ S s := fun {s S} => by
    have h := proj_inj S
    dsimp [σ, τ]
    rw [h]
  let ω : Set (Set U) := fun p => ∀ x, σ x p → p x
  let δ (S : Set (Set U)) := ∀ p, S p → p (τ S)
  have h_delta_omega : δ ω := fun p hp => hp (τ ω) (στ.mpr hp)
  let p0 : Set U := fun y => ¬ δ (σ y)
  have h_omega_p0 : ω p0 := by
    intro x hx h_delta
    have h_not : p0 (τ (σ x)) := h_delta p0 hx
    have h_eq : σ (τ (σ x)) = σ x := by
      ext y
      exact στ
    rw [h_eq] at h_not
    exact h_not h_delta
  have h_not_delta_omega : ¬ δ ω := by
    have h_not : p0 (τ ω) := h_omega_p0 (τ ω) (by
      rw [στ]
      exact h_omega_p0
    )
    have h_eq : σ (τ ω) = ω := by
      ext y
      exact στ
    rw [h_eq] at h_not
    exact h_not
  exact h_not_delta_omega h_delta_omega
