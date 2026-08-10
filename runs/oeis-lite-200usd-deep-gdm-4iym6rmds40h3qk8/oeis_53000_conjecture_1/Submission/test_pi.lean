inductive pi (A : Type → Type) : Type 1
| mk : (∀ x, A x) → pi A

def decomp {A : Type → Type} : pi A → (∀ x, A x)
| pi.mk f => f

def lam {A : Type → Type} (f : ∀ x, A x) : pi A := pi.mk f

def app {A : Type → Type} (p : pi A) : ∀ x, A x := decomp p

theorem beta {A : Type → Type} (f : ∀ x, A x) (x : Type) : app (lam f) x = f x := rfl

def Set (X : Type u) : Type u := X → Prop

def F (X : Type) : Type := (Set (Set X) → X) → Set (Set X)

theorem girard : False := by
  let U : Type 1 := pi F
  let G (T : Set (Set U)) (X : Type) : F X := fun f => fun p => T (fun x => p (f (app x X f)))
  let τ (T : Set (Set U)) : U := lam (G T)
  let σ (S : U) : Set (Set U) := app S U τ
  have στ : ∀ (s : Set U) (S : Set (Set U)), σ (τ S) s ↔ S (fun x => s (τ (σ x))) := fun s S =>
    Iff.rfl
  let ω : Set (Set U) := fun p => ∀ x, σ x p → p x
  let δ (S : Set (Set U)) := ∀ p, S p → p (τ S)
  have h_delta : δ ω := fun _p d => d (τ ω) <| (στ _ _).2 fun x h => d (τ (σ x)) ((στ _ _).2 h)
  exact h_delta (fun y => ¬δ (σ y)) (fun _x e f => f _ e fun _p h => f _ ((στ _ _).1 h)) fun _p h => h_delta _ ((στ _ _).1 h)


