def Set (X : Prop) : Type 0 := X → Prop

def F (X : Prop) : Type 0 := (Set (Set X) → X) → Set (Set X)

inductive Unsound : Type 0
| mk : (∀ X : Prop, F X) → Unsound

abbrev U := Unsound

def decomp : U → (∀ X : Prop, F X)
| Unsound.mk f => f

def lam (f : ∀ X : Prop, F X) : U := Unsound.mk f

def app (u : U) (X : Prop) : F X := decomp u X

theorem beta (f : ∀ X : Prop, F X) (X : Prop) : app (lam f) X = f X := rfl

theorem girard : False := by
  let G (T : Set (Set U)) (X : Prop) : F X := fun f => fun p => T (fun x => p (f (app x X f)))
  let τ (T : Set (Set U)) : U := lam (G T)
  let σ (S : U) : Set (Set U) := app S U τ
  have στ : ∀ (s : Set U) (S : Set (Set U)), σ (τ S) s ↔ S (fun x => s (τ (σ x))) := fun s S =>
    Iff.rfl
  let ω : Set (Set U) := fun p => ∀ x, σ x p → p x
  let δ (S : Set (Set U)) := ∀ p, S p → p (τ S)
  have h_delta : δ ω := fun _p d => d (τ ω) <| (στ _ _).2 fun x h => d (τ (σ x)) ((στ _ _).2 h)
  exact h_delta (fun y => ¬δ (σ y)) (fun _x e f => f _ e fun _p h => f _ ((στ _ _).1 h)) fun _p h => h_delta _ ((στ _ _).1 h)
