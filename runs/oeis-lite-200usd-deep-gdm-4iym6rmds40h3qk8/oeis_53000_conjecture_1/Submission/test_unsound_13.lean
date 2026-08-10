set_option bootstrap.inductive_universe_restriction false

inductive Bad (F : Type 0 → Type 0) : Type 0
| mk : (∀ X : Type 0, F X) → Bad F

def F (X : Type 0) : Type 0 := (((X → Prop) → Prop) → X) → ((X → Prop) → Prop)

abbrev U := Bad F

def decomp : U → (∀ X : Type 0, F X)
| Bad.mk f => f

def lam (f : ∀ X : Type 0, F X) : U := Bad.mk f

def app (u : U) (X : Type 0) : F X := decomp u X

theorem beta (f : ∀ X : Type 0, F X) (X : Type 0) : app (lam f) X = f X := rfl

def G (T : (U → Prop) → Prop) (X : Type 0) : F X :=
  fun f p => T (fun x => p (f (app x X f)))

def τ (T : (U → Prop) → Prop) : U := lam (G T)

def σ (S : U) : (U → Prop) → Prop := app S U τ

theorem στ (s : U → Prop) (S : (U → Prop) → Prop) : σ (τ S) s ↔ S (fun x => s (τ (σ x))) :=
  Iff.rfl


