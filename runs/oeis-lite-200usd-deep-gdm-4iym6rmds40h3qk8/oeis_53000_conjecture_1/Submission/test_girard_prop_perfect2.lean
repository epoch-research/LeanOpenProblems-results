def Set (X : Prop) : Prop := X → False

def F (X : Type 0) : Prop := (Set (Set X) → X) → Set (Set X)

inductive Unsound : Prop
| mk : (∀ X : Type 0, F X) → Unsound

abbrev U := Unsound

def decomp : U → (∀ X : Type 0, F X)
| Unsound.mk f => f

def lam (f : ∀ X : Type 0, F X) : U := Unsound.mk f

def app (u : U) (X : Type 0) : F X := decomp u X

theorem beta (f : ∀ X : Type 0, F X) (X : Type 0) : app (lam f) X = f X := rfl

abbrev U0 := PLift U

noncomputable def G (T : Set (Set U0)) (X : Type 0) : F X :=
  fun f => fun p => T (fun x => p (f (app (PLift.down x) X f)))

noncomputable def τ (T : Set (Set U0)) : U := lam (G T)

noncomputable def σ (S : U0) : Set (Set U0) :=
  app (PLift.down S) U0 (fun f => PLift.up (τ f))

theorem στ (s : Set U0) (S : Set (Set U0)) :
  σ (PLift.up (τ S)) s ↔ S (fun x => s (PLift.up (τ (σ x)))) := Iff.rfl
