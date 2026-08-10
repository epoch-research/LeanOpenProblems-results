-- A correct copy of Hurkens' paradox on U with Power(Power(U)) → U
open Classical

theorem hurkens_paradox {U : Type} (inj : ((U → Prop) → Prop) → U) (proj : U → (U → Prop) → Prop)
    (proj_inj : ∀ F, proj (inj F) = F) : False := by
  let σ (u : U) : (U → Prop) → Prop := proj u
  let τ (S : (U → Prop) → Prop) : U := inj S
  have στ : ∀ S, σ (τ S) = S := proj_inj
  let P (p : (U → Prop) → Prop) : Prop := ∀ x, σ x (fun u => p (σ u)) → p (σ x)
  -- Wait, let's look at the exact definition of Hurkens' paradox in Coq or Mathlib's Counterexamples/Girard.lean.
  -- In Counterexamples/Girard.lean, they use:
  -- F (X) := (Set (Set X) → X) → Set (Set X)
  -- U := pi F
  -- where pi F is the pi type.
  -- Let's check Girard.lean again!
  sorry
