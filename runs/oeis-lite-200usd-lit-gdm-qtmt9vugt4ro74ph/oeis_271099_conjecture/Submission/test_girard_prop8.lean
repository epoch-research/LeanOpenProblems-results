import Mathlib

set_option linter.unusedVariables false

def my_pi (A : Type → Type) : Type 1 := ∀ x, A x
def my_lam {A : Type → Type} (f : ∀ x, A x) : my_pi A := f
def my_app {A} (f : my_pi A) (x : Type) : A x := f x
def my_beta {A : Type → Type} (f : ∀ x, A x) (x : Type) : my_app (my_lam f) x = f x := rfl

def F (X : Type) : Type := (((X → Prop) → Prop) → X) → ((X → Prop) → Prop)
def U : Type 1 := my_pi F

def G (T : (U → Prop) → Prop) (X : Type) : F X :=
  fun f p => T (fun x => p (f (my_app x X f)))

def τ (T : (U → Prop) → Prop) : U := my_lam (G T)
def σ (S : U) : (U → Prop) → Prop := my_app S U τ

theorem στ (s : U → Prop) (S : (U → Prop) → Prop) : σ (τ S) s ↔ S (fun x => s (τ (σ x))) :=
  iff_of_eq (congr_arg (fun f : F U => s (f τ)) (my_beta (G S) U))

noncomputable def ω : (U → Prop) → Prop :=
  fun p => ∀ x : U, σ x p → p x

noncomputable def δ (S : (U → Prop) → Prop) : Prop :=
  ∀ p : U → Prop, S p → p (τ S)

theorem proof_of_false : False := by
  have h_delta : δ ω := fun p d => d (τ ω) <| (στ p ω).mpr fun x h => d (τ (σ x)) ((στ p (σ x)).mpr h)
  exact h_delta (fun y => ¬ δ (σ y))
    (fun x e f => f x e fun p h => f p ((στ p (σ x)).mp h))
    fun p h => h_delta p ((στ p ω).mp h)
