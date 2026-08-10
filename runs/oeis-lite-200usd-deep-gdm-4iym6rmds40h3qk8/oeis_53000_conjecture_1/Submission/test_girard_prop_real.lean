def Set (X : Prop) : Prop := X → Prop

def Set_Prop (X : Prop) : Prop := Set X → Prop

def F (X : Prop) : Prop := (Set_Prop X → X) → Set_Prop X

inductive Unsound : Prop
| mk : (∀ X : Prop, F X) → Unsound

abbrev U := Unsound

def decomp : U → (∀ X : Prop, F X)
| Unsound.mk f => f

def lam (f : ∀ X : Prop, F X) : U := Unsound.mk f

def app (u : U) (X : Prop) : F X := decomp u X

theorem beta (f : ∀ X : Prop, F X) (X : Prop) : app (lam f) X = f X := rfl

open Classical

theorem girard : False := by
  let G (T : Set_Prop U) (X : Prop) : F X := fun f => fun p => T (fun x => p (f (app x X f)))
  let τ (T : Set_Prop U) : U := lam (G T)
  let σ (S : U) : Set_Prop U := app S U τ
  have στ : ∀ {s S}, s ∈ σ (τ S) ↔ {x | τ (σ x) ∈ s} ∈ S := fun {s S} =>
    Iff.rfl
  let ω : Set_Prop U := fun p => ∀ x, p ∈ σ x → x ∈ p
  let δ (S : Set_Prop U) := ∀ p, p ∈ S → τ S ∈ p
  have h_delta : δ ω := fun _p d => d (τ ω) <| στ.2 fun x h => d (τ (σ x)) (στ.2 h)
  exact h_delta (fun y => ¬δ (σ y)) (fun _x e f => f _ e fun _p h => f _ (στ.1 h)) fun _p h => h_delta _ (στ.1 h)
