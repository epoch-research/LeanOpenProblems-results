-- Let's formalize Hurkens' paradox using an abstract type U with injection/projection
-- to show how it can be proven in Lean.
open Classical

variable {U : Type}
variable (inj : ((U → Prop) → Prop) → U)
variable (proj : U → (U → Prop) → Prop)
variable (proj_inj : ∀ F, proj (inj F) = F)

theorem hurkens_paradox : False := by
  let F (X : Type) : Type := ((X → Prop) → Prop) → (X → Prop) → Prop
  -- Let's directly adapt the standard Hurkens' proof
  -- We have an injection from Power(Power(U)) to U, which is:
  -- proj : U → Power(Power(U))
  -- inj : Power(Power(U)) → U
  -- such that proj ∘ inj = id.
  -- Let's define:
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
      rw [στ]
      exact fun y hy => hnotδ (by
        -- wait, we can just rewrite using στ
        sorry
      )
    ))
  exact hnotδ hδ
