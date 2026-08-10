import FormalConjectures.Util.ProblemImports

theorem prop_girard : False := by
  let F (X : Prop) := (((X → Prop) → Prop) → X) → ((X → Prop) → Prop)
  let U := ∀ X : Prop, F X
  let G (T : ((U → Prop) → Prop)) (X : Prop) : F X := fun f => fun p => T (fun (x : U) => p (f (x X f)))
  let τ (T : ((U → Prop) → Prop)) : U := fun X => G T X
  let σ (S : U) : ((U → Prop) → Prop) := S U τ
  have στ : ∀ {s S}, σ (τ S) s ↔ S (fun x => s (τ (σ x))) := fun {s S} =>
    Iff.rfl
  let ω : ((U → Prop) → Prop) := fun p => ∀ x, σ x p → p x
  let δ (S : ((U → Prop) → Prop)) := ∀ p, S p → p (τ S)
  have hδ : δ ω := fun _p d => d (τ ω) <| στ.2 fun x h => d (τ (σ x)) (στ.2 h)
  exact hδ (fun y => ¬δ (σ y)) (fun _x e f => f _ e fun _p h => f _ (στ.1 h)) fun _p h => hδ _ (στ.1 h)
