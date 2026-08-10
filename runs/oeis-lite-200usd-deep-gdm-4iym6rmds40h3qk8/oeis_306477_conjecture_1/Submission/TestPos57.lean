open Classical

theorem hurkens_paradox {U : Type} (inj : ((U → Prop) → Prop) → U) (proj : U → (U → Prop) → Prop)
    (proj_inj : ∀ F, proj (inj F) = F) : False := by
  let σ (u : U) : (U → Prop) → Prop := proj u
  let τ (S : (U → Prop) → Prop) : U := inj S
  have στ : ∀ S, σ (τ S) = S := proj_inj
  let ω : (U → Prop) → Prop := fun p => ∀ x, σ x p → p x
  let δ (S : (U → Prop) → Prop) : Prop := ∀ p, S p → p (τ S)
  have hδ : δ ω := fun p hp => hp (τ ω) (by
    rw [στ]
    exact fun x hx => hp x hx
  )
  have hnotδ : ¬ δ ω := fun h =>
    h (fun x => ¬ δ (σ x)) (fun x hx => hx (fun y => ¬ δ (σ y)) (by
      -- wait, we can just rewrite using στ
      sorry
    ))
  exact hnotδ hδ
