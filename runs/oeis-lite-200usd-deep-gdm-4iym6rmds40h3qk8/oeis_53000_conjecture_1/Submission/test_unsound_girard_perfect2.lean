def Set (X : Type 0) : Type 0 := X → Prop

def Set_Prop (X : Type 0) : Type 0 := Set X → Prop

def F (X : Type 0) : Type 0 := (Set_Prop X → X) → Set_Prop X

inductive Unsound : Type 0
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
  have στ : ∀ (s : Set U) (S : Set_Prop U), σ (τ S) s ↔ S (fun x => s (τ (σ x))) := fun s S =>
    Iff.rfl
  let ω : Set_Prop U := fun p => ∀ x, σ x p → p x
  let δ (S : Set_Prop U) := ∀ p, S p → p (τ S)
  have h_delta : δ ω := fun _p d => d (τ ω) <| (Iff.mp (στ _ _)) fun x h => d (τ (σ x)) ((Iff.mpr (στ _ _)) h)
  exact h_delta (fun y => ¬δ (σ y)) (fun _x e f => f _ e fun _p h => f _ ((Iff.mp (στ _ _)) h)) fun _p h => h_delta _ ((Iff.mp (στ _ _)) h)
