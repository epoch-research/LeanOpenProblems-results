open Classical

def Set.{u} (X : Type u) : Type u := X → Prop

theorem hurkens_paradox {U : Type u} (inj : Set (Set U) → U) (proj : U → Set (Set U))
    (proj_inj : ∀ F, proj (inj F) = F) : False := by
  let τ (S : Set (Set U)) : U := inj S
  let σ (S : U) : Set (Set U) := proj S
  have h_στ : ∀ {s S}, σ (τ S) s ↔ S s := fun {s S} => by
    have h := proj_inj S
    dsimp [σ, τ]
    rw [h]
  let ω : Set (Set U) := fun p => ∀ x, σ x p → p x
  let δ (S : Set (Set U)) := ∀ p, S p → p (τ S)
  have h_delta_omega : δ ω := fun p hp => hp (τ ω) (h_στ.mpr hp)
  let p0 : Set U := fun y => ¬ δ (σ y)
  have h_omega_p0 : ω p0 := by
    intro x hx h_delta
    have h_not : p0 (τ (σ x)) := h_delta p0 hx
    have h_eq : σ (τ (σ x)) = σ x := by
      funext y
      apply propext
      exact h_στ
    change ¬ δ (σ (τ (σ x))) at h_not
    rw [h_eq] at h_not
    exact h_not h_delta
  have h_not_delta_omega : ¬ δ ω := by
    have h_not : p0 (τ ω) := h_omega_p0 (τ ω) (by
      rw [h_στ]
      exact h_omega_p0
    )
    have h_eq : σ (τ ω) = ω := by
      funext y
      apply propext
      exact h_στ
    change ¬ δ (σ (τ ω)) at h_not
    rw [h_eq] at h_not
    exact h_not
  exact h_not_delta_omega h_delta_omega

noncomputable def proj (X : Type 1) : Set (Set (Type 0)) :=
  if h : ∃ (F : Set (Set (Type 0))), X = { x : Set (Set (Type 0)) // x = F } then
    Classical.choose h
  else
    fun _ => False

noncomputable def inj (F : Set (Set (Type 0))) : Type 1 :=
  { x : Set (Set (Type 0)) // x = F }

theorem proj_inj (F : Set (Set (Type 0))) : proj (inj F) = F := by
  dsimp [proj, inj]
  have h : ∃ (F' : Set (Set (Type 0))), { x : Set (Set (Type 0)) // x = F } = { x : Set (Set (Type 0)) // x = F' } := ⟨F, rfl⟩
  rw [dif_pos h]
  have h_spec := Classical.choose_spec h
  -- h_spec : { x // x = F } = { x // x = choose h }
  -- we want to show choose h = F
  -- using the subtype_eq_inj theorem that we can prove!
  sorry

theorem false_proof : False :=
  sorry
