import Mathlib.Logic.Basic
import Mathlib.Data.Set.Defs

inductive pi (A : Type 1 → Type 1) : Type 1
| mk : (∀ x, A x) → pi A

def decomp {A : Type 1 → Type 1} : pi A → (∀ x, A x)
| pi.mk f => f

def lam {A : Type 1 → Type 1} (f : ∀ x, A x) : pi A := pi.mk f

def app {A : Type 1 → Type 1} (p : pi A) : ∀ x, A x := decomp p

theorem beta {A : Type 1 → Type 1} (f : ∀ x, A x) (x : Type 1) : app (lam f) x = f x := rfl

theorem unsound : False := by
  let F (X) := (Set (Set X) → X) → Set (Set X)
  let U := pi F
  let G (T : Set (Set U)) (X) : F X := fun f => {p | {x : U | f (app x X f) ∈ p} ∈ T}
  let τ (T : Set (Set U)) : U := lam (G T)
  let σ (S : U) : Set (Set U) := app S U τ
  have στ : ∀ {s S}, s ∈ σ (τ S) ↔ {x | τ (σ x) ∈ s} ∈ S := fun {s S} =>
    iff_of_eq (congr_arg (fun f : F U => s ∈ f τ) (beta (G S) U) :)
  let ω : Set (Set U) := {p | ∀ x, p ∈ σ x → x ∈ p}
  let δ (S : Set (Set U)) := ∀ p, p ∈ S → τ S ∈ p
  have h_delta : δ ω := fun _p d => d (τ ω) <| στ.2 fun x h => d (τ (σ x)) (στ.2 h)
  exact h_delta {y | ¬δ (σ y)} (fun _x e f => f _ e fun _p h => f _ (στ.1 h)) fun _p h => h_delta _ (στ.1 h)
