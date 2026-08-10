def Set (X : Prop) : Type 0 := X → Prop

def Set_Prop (X : Prop) : Prop := Set X → False

def F (X : Prop) : Prop := (Set_Prop X → X) → Set_Prop X

inductive Unsound : Prop
| mk : (∀ X : Prop, F X) → Unsound

theorem unsound_eq : Unsound ↔ (∀ X : Prop, F X) := by
  constructor
  · intro u
    cases u with
    | mk f => exact f
  · exact Unsound.mk

theorem unsound_eq_prop : Unsound = (∀ X : Prop, F X) :=
  propext unsound_eq

def decomp : Unsound → (∀ X : Prop, F X) := cast unsound_eq_prop

def lam (f : ∀ X : Prop, F X) : Unsound := Unsound.mk f

def app (u : Unsound) (X : Prop) : F X := decomp u X

theorem beta (f : ∀ X : Prop, F X) (X : Prop) : app (lam f) X = f X := rfl

abbrev U := Unsound

def G (T : Set_Prop U) (X : Prop) : F X :=
  fun f p => T (fun u => p (f (fun q => app u X f q)))

def τ (T : Set_Prop U) : U := lam (G T)

def σ (S : U) : Set_Prop U := app S U τ

theorem στ (s : Set U) (S : Set_Prop U) : σ (τ S) s ↔ S (fun x => s (τ (σ x))) := by
  dsimp [σ, τ, lam, app, decomp, G]
  exact Iff.rfl

def ω : Set_Prop U := fun p => ∀ x, σ x p → p x

def δ (S : Set_Prop U) : Prop := ∀ p, S p → p (τ S)

theorem h_delta : δ ω := by
  intro p d
  apply d (τ ω)
  rw [στ]
  intro x h
  apply d (τ (σ x))
  rw [στ]
  exact h

theorem unsound : False := by
  have h_omega : ω (fun y => ¬ δ (σ y)) := by
    intro x e f
    exact f _ e fun p h => f _ ((στ _ _).mp h)
  exact h_omega (τ ω) ((στ _ _).mpr fun x h => h_delta _ ((στ _ _).mp h)) h_delta
