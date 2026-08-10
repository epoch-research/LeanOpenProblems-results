def Set (X : Type u) : Type u := X → Prop

def Set_Prop (X : Type u) : Type u := Set X → Prop

def F (X : Type u) : Type u := (Set_Prop X → X) → Set_Prop X

inductive Unsound : Type 1
| mk : (∀ X : Type 0, F X) → Unsound

abbrev U := Unsound

def decomp : U → (∀ X : Type 0, F X)
| Unsound.mk f => f

def lam (f : ∀ X : Type 0, F X) : U := Unsound.mk f

def app (u : U) (X : Type 0) : F X := decomp u X

theorem beta (f : ∀ X : Type 0, F X) (X : Type 0) : app (lam f) X = f X := rfl

theorem girard : False := by
  let G (T : Set_Prop U) (X : Type 0) : F X := fun f => fun p => T (fun x => p (f (app x X f)))
  let τ (T : Set_Prop U) : U := lam (G T)
  let σ (S : U) : Set_Prop U := app S U τ
  sorry
