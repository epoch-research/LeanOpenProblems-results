def Set (X : Type 0) : Type 0 := X → Prop

def Set_Prop (X : Type 0) : Type 0 := Set X → Prop

def F (X : Type 0) : Type 0 := (Set_Prop X → X) → Set_Prop X

inductive Unsound : Type 0
| mk : (∀ X : Prop, F X) → Unsound

abbrev U := Unsound

def decomp : U → (∀ X : Prop, F X)
| Unsound.mk f => f

def lam (f : ∀ X : Prop, F X) : U := Unsound.mk f

def app (u : U) (X : Prop) : F X := decomp u X

theorem beta (f : ∀ X : Prop, F X) (X : Prop) : app (lam f) X = f X := rfl

def G (T : Set_Prop U) (X : Prop) : F X :=
  fun f p => T (fun u => p (f (fun q => app u X f q)))

def τ (T : Set_Prop U) : U := lam (G T)

def σ (S : U) : Set_Prop U := app S U τ

def ω : Set_Prop U := fun p => ∀ x, σ x p → p x

def δ (S : Set_Prop U) : Prop := ∀ p, S p → p (τ S)

theorem h_delta : δ ω := by
  intro p d
  have h1 : σ (τ ω) p := by
    intro x h
    exact d (τ (σ x)) h
  exact d (τ ω) h1

theorem unsound : False := by
  have h_omega : ω (fun y => ¬ δ (σ y)) := by
    intro x e f
    exact f _ e fun p h => f _ h
  exact h_omega (τ ω) h_omega h_delta
