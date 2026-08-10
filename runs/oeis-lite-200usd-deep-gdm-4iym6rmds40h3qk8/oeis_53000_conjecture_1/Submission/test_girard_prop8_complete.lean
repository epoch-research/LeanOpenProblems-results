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

open Classical

theorem girard : False := by
  let G (T : Set_Prop U) (X : Prop) : F X := fun f => fun p => T (fun x => p (f (fun q => app x X f q)))
  let τ (T : Set_Prop U) : U := lam (G T)
  let σ (S : U) : Set_Prop U := app S U τ
  have στ : ∀ (s : Set U) (S : Set_Prop U), σ (τ S) s ↔ S (fun x => s (τ (σ x))) := fun s S =>
    Iff.rfl
  let ω : Set_Prop U := fun p => ∀ x, σ x p → p x
  let δ (S : Set_Prop U) := ∀ p, S p → p (τ S)
  have h_delta : δ ω := fun _p d => d (τ ω) <| (Iff.mp (στ _ _)) fun x h => d (τ (σ x)) ((Iff.mpr (στ _ _)) h)
  exact h_delta (fun y => ¬δ (σ y)) (fun _x e f => f _ e fun _p h => f _ ((Iff.mp (στ _ _)) h)) fun _p h => h_delta _ ((Iff.mp (στ _ _)) h)
