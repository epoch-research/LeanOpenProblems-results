import FormalConjectures.Util.ProblemImports

theorem prop_girard : False := by
  let F (X : Prop) := (((X → Prop) → Prop) → X) → ((X → Prop) → Prop)
  let U := ∀ X : Prop, F X
  let G (T : (U → Prop) → Prop) (X : Prop) : F X := fun f => fun p => {x : U | f (x X f) ∈ p} ∈ T
  let τ (T : (U → Prop) → Prop) : U := fun X => G T X
  let σ (S : U) : (U → Prop) → Prop := S U τ
  have στ : ∀ {s S}, s ∈ σ (τ S) ↔ {x | τ (σ x) ∈ s} ∈ S := fun {s S} =>
    Iff.rfl
  let ω : (U → Prop) → Prop := fun p => ∀ x, p ∈ σ x → x ∈ p
  let δ (S : (U → Prop) → Prop) := ∀ p, p ∈ S → τ S ∈ p
  have hδ : δ ω := fun _p d => d (τ ω) <| στ.2 fun x h => d (τ (σ x)) (στ.2 h)
  exact hδ (fun y => ¬δ (σ y)) (fun _x e f => f _ e fun _p h => f _ (στ.1 h)) fun _p h => hδ _ (στ.1 h)
