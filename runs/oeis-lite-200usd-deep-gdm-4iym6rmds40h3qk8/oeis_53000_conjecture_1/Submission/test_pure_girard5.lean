def Set (X : Type 0) : Type 0 := X → Prop

def Set_Prop (X : Type 0) : Type 0 := Set X → Prop

def F (X : Type 0) : Type 0 := (Set_Prop X → X) → Set_Prop X

inductive Unsound : Type 1
| mk : (∀ X : Type 0, F X) → Unsound

abbrev U := Unsound

def decomp : U → (∀ X : Type 0, F X)
| Unsound.mk f => f

def lam (f : ∀ X : Type 0, F X) : U := Unsound.mk f

def app (u : U) (X : Type 0) : F X := decomp u X

theorem beta (f : ∀ X : Type 0, F X) (X : Type 0) : app (lam f) X = f X := rfl

open Classical

abbrev U0 := PLift U

noncomputable def G (T : Set_Prop U0) (X : Type 0) : F X :=
  fun f p => T (fun (u : U0) => p (f (fun q => app u.down X f q)))

noncomputable def τ (T : Set_Prop U0) : U0 :=
  PLift.up (lam (G T))

noncomputable def σ (S : U0) : Set_Prop U0 :=
  app S.down U0 (fun T => τ (PLift.down T))
