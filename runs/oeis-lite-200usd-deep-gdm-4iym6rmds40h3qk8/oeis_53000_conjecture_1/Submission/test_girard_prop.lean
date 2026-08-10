def pi (A : Prop → Prop) : Prop := ∀ x : Prop, A x

def lam {A : Prop → Prop} (f : ∀ x, A x) : pi A := f

def app {A : Prop → Prop} (p : pi A) : ∀ x, A x := p

theorem beta {A : Prop → Prop} (f : ∀ x, A x) (x : Prop) : app (lam f) x = f x := rfl

def Set (X : Prop) : Prop := X → False

def F (X : Prop) : Prop := (Set (Set X) → X) → Set (Set X)

theorem girard : False := by
  let U : Prop := pi F
  let G (T : Set (Set U)) (X : Prop) : F X := fun f => fun p => T (fun x => p (f (app x X f)))
  let τ (T : Set (Set U)) : U := lam (G T)
  let σ (S : U) : Set (Set U) := app S U τ
  have στ : ∀ (s : Set U) (S : Set (Set U)), σ (τ S) s ↔ S (fun x => s (τ (σ x))) := fun s S => by
    -- wait, can we prove this?
    sorry
  let ω : Set (Set U) := fun p => ∀ x, σ x p → p x
  let δ (S : Set (Set U)) := ∀ p, S p → p (τ S)
  have h_delta : δ ω := fun _p d => d (τ ω) <| (στ _ _).2 fun x h => d (τ (σ x)) ((στ _ _).2 h)
  exact h_delta (fun y => ¬δ (σ y)) (fun _x e f => f _ e fun _p h => f _ ((στ _ _).1 h)) fun _p h => h_delta _ ((στ _ _).1 h)
