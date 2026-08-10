def Set (X : Prop) : Type 0 := X → Prop

def Set_Prop (X : Prop) : Type 0 := Set X → Prop

def F (X : Prop) : Type 0 := (Set_Prop X → X) → Set_Prop X

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

theorem στ (s : Set U) (S : Set_Prop U) : σ (τ S) s ↔ S (fun x => s (τ (σ x))) := by
  dsimp [σ, τ, lam, app, decomp, G]
  exact Iff.rfl
