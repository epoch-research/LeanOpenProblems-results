def Set (X : Type 0) : Type 0 := X → Prop

def Set_Prop (X : Type 0) : Type 0 := Set X → Prop

def F_Type (X : Type 0) : Type 0 := (Set_Prop X → X) → Set_Prop X

def F (X : Prop) : Type 0 := F_Type (PLift X)

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
