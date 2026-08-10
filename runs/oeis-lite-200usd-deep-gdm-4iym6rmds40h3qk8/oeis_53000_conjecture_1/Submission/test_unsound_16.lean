inductive Unsound : Prop
| mk : (Type 0 → Unsound) → Unsound
| base : Unsound

abbrev U := Unsound

def decomp : U → (Type 0 → U)
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f

def lam (f : Type 0 → U) : U := Unsound.mk f

def app (u : U) (X : Type 0) : U := decomp u X

theorem beta (f : Type 0 → U) (X : Type 0) : app (lam f) X = f X := rfl

def Set (X : Type) : Type := X → Prop

def F (X : Type) : Type := (Set (Set X) → X) → Set (Set X)

theorem girard : False := by
  let G (T : Set (Set U)) (X : Type) : F X := fun f => fun p => T (fun x => p (f (app x X f)))
  let τ (T : Set (Set U)) : U := lam (G T)
  let σ (S : U) : Set (Set U) := app S U τ
  have στ : ∀ (s : Set U) (S : Set (Set U)), σ (τ S) s ↔ S (fun x => s (τ (σ x))) := fun s S =>
    Iff.rfl
  let ω : Set (Set U) := fun p => ∀ x, σ x p → p x
  let δ (S : Set (Set U)) := ∀ p, S p → p (τ S)
  have h_delta : δ ω := fun _p d => d (τ ω) <| (στ _ _).2 fun x h => d (τ (σ x)) ((στ _ _).2 h)
  exact h_delta (fun y => ¬δ (σ y)) (fun _x e f => f _ e fun _p h => f _ ((στ _ _).1 h)) fun _p h => h_delta _ ((στ _ _).1 h)


-- Wait, U has type Prop, but Prop has type Type 0, so U has type Type 0!
-- So we can pass U as Type 0!
