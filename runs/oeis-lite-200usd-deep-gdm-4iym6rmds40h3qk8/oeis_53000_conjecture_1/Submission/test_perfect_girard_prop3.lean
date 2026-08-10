def Set (X : Prop) : Type 0 := X → Prop

def Set_Prop (X : Prop) : Prop := Set X → False

def F (X : Prop) : Prop := (Set_Prop X → X) → Set_Prop X

inductive Unsound : Prop
| mk : (∀ X : Prop, F X) → Unsound
| base : Unsound

abbrev U := Unsound

partial def decomp : U → (∀ X : Prop, F X)
| Unsound.base => decomp Unsound.base
| Unsound.mk f => f

def lam (f : ∀ X : Prop, F X) : U := Unsound.mk f

def app (u : U) (X : Prop) : F X := decomp u X

theorem beta (f : ∀ X : Prop, F X) (X : Prop) : app (lam f) X = f X := rfl

theorem girard : False := by
  let G (T : Set_Prop U) (X : Prop) : F X := fun f => fun p => T (fun x => p (f (fun h => app x X f)))
  let τ (T : Set_Prop U) : U := lam (G T)
  let σ (S : U) : Set_Prop U := app S U τ
  have στ : ∀ (s : Set U) (S : Set_Prop S), σ (τ S) s ↔ S (fun x => s (τ (σ x))) := fun s S =>
    Iff.rfl
  sorry
