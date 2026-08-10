def Set (X : Type 0) : Type 0 := X → Prop

def Set_Prop (X : Type 0) : Type 0 := Set X → Prop

def F (X : Type 0) : Type 0 := (Set_Prop X → X) → Set_Prop X

inductive Bad : Type 1
| mk : (∀ (X : Type 0), F X) → Bad

abbrev U := Bad

def decomp : Bad → (∀ (X : Type 0), F X)
| Bad.mk f => f

def lam (f : ∀ (X : Type 0), F X) : Bad :=
  Bad.mk f

def app (b : Bad) (X : Type 0) : F X :=
  decomp b X

theorem beta (f : ∀ (X : Type 0), F X) (X : Type 0) : app (lam f) X = f X := rfl

abbrev U0 := PLift U

def G (T : Set_Prop U0) (X : Type 0) : F X :=
  fun f p => T (fun u => p (f (fun q => app u.down X f q)))

def τ (T : Set_Prop U0) : U0 := PLift.up (lam (G T))

def σ (S : U0) : Set_Prop U0 := app S.down U0 τ

theorem στ (s : Set U0) (S : Set_Prop U0) : σ (τ S) s ↔ S (fun x => s (τ (σ x))) := by
  dsimp [σ, τ, lam, app, decomp, G]
  exact Iff.rfl
