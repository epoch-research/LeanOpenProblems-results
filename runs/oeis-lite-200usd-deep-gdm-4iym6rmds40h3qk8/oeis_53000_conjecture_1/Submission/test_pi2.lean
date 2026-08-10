inductive pi (A : Type 1 → Prop) : Prop
| mk : (∀ x, A x) → pi A

def decomp {A : Type 1 → Prop} : pi A → (∀ x, A x)
| pi.mk f => f

def lam {A : Type 1 → Prop} (f : ∀ x, A x) : pi A := pi.mk f

def app {A : Type 1 → Prop} (p : pi A) : ∀ x, A x := decomp p

theorem beta {A : Type 1 → Prop} (f : ∀ x, A x) (x : Type 1) : app (lam f) x = f x := rfl

def Set (X : Type 1) : Type 1 := X → Prop

-- Note that Set X is in Type 1, but Set_Prop below is in Prop!
def Set_Prop (X : Type 1) : Prop := Set X → Prop

def F (X : Type 1) : Prop := (Set_Prop X → X) → Set_Prop X

theorem girard : False := by
  let U : Type 1 := pi F
  let G (T : Set_Prop U) (X : Type 1) : F X := fun f => fun p => T (fun x => p (f (app x X f)))
  let τ (T : Set_Prop U) : U := lam (G T)
  let σ (S : U) : Set_Prop U := app S U τ
  have στ : ∀ (s : Set U) (S : Set_Prop U), σ (τ S) s ↔ S (fun x => s (τ (σ x))) := fun s S =>
    Iff.rfl
  let ω : Set_Prop U := fun p => ∀ x, σ x p → p x
  let δ (S : Set_Prop U) := ∀ p, S p → p (τ S)
  have h_delta : δ ω := fun _p d => d (τ ω) <| (στ _ _).2 fun x h => d (τ (σ x)) ((στ _ _).2 h)
  exact h_delta (fun y => ¬δ (σ y)) (fun _x e f => f _ e fun _p h => f _ ((στ _ _).1 h)) fun _p h => h_delta _ ((στ _ _).1 h)

