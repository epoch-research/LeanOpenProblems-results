import FormalConjectures.Util.ProblemImports

theorem prop_girard : False := by
  let F (X : Prop) := (Set (Set X) → X) → Set (Set X)
  let U := ∀ X : Prop, F X
  let G (T : Set (Set U)) (X : Prop) : F X := fun f => {p | {x : U | f (x X f) ∈ p} ∈ T}
  let τ (T : Set (Set U)) : U := fun X => G T X
  let σ (S : U) : Set (Set U) := S U τ
  have στ : ∀ {s S}, s ∈ σ (τ S) ↔ {x | τ (σ x) ∈ s} ∈ S := fun {s S} =>
    Iff.rfl
  let ω : Set (Set U) := {p | ∀ x, p ∈ σ x → x ∈ p}
  let δ (S : Set (Set U)) := ∀ p, p ∈ S → τ S ∈ p
  have hδ : δ ω := fun _p d => d (τ ω) <| στ.2 fun x h => d (τ (σ x)) (στ.2 h)
  exact hδ {y | ¬δ (σ y)} (fun _x e f => f _ e fun _p h => f _ (στ.1 h)) fun _p h => hδ _ (στ.1 h)
