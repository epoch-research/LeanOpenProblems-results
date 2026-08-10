inductive Unsound : Prop
| mk : (Type 0 → Unsound) → Unsound
| base : Unsound

abbrev U := Unsound

def decomp : U → (Type 0 → U)
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f

abbrev U_type : Type 0 := PLift U

def lam (f : Type 0 → U_type) : U_type :=
  PLift.up (Unsound.mk (fun X => PLift.down (f X)))

def app (u : U_type) (X : Type 0) : U_type :=
  PLift.up (decomp (PLift.down u) X)

theorem beta (f : Type 0 → U_type) (X : Type 0) : app (lam f) X = f X := rfl

def Set (X : Type 0) : Type 0 := X → Prop

def F (X : Type 0) : Type 0 := (Set (Set X) → X) → Set (Set X)

theorem girard : False := by
  let G (T : Set (Set U_type)) (X : Type 0) : F X := fun f => fun p => T (fun x => p (f (app x X f)))
  let τ (T : Set (Set U_type)) : U_type := lam (G T)
  let σ (S : U_type) : Set (Set U_type) := app S U_type τ
  have στ : ∀ (s : Set U_type) (S : Set (Set U_type)), σ (τ S) s ↔ S (fun x => s (τ (σ x))) := fun s S =>
    Iff.rfl
  let ω : Set (Set U_type) := fun p => ∀ x, σ x p → p x
  let δ (S : Set (Set U_type)) := ∀ p, S p → p (τ S)
  have h_delta : δ ω := fun _p d => d (τ ω) <| (στ _ _).2 fun x h => d (τ (σ x)) ((στ _ _).2 h)
  exact h_delta (fun y => ¬δ (σ y)) (fun _x e f => f _ e fun _p h => f _ ((Iff.mp (στ _ _)) h)) fun _p h => h_delta _ ((Iff.mp (στ _ _)) h)
