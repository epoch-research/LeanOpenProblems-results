import Mathlib.Logic.Basic
import Mathlib.Data.Set.Defs
import Counterexamples.Girard

inductive pi (A : Type 1 → Type 1) : Type 1
| mk : (∀ x, A x) → pi A

def decomp {A : Type 1 → Type 1} : pi A → (∀ x, A x)
| pi.mk f => f

def lam {A : Type 1 → Type 1} (f : ∀ x, A x) : pi A := pi.mk f

def app {A : Type 1 → Type 1} (p : pi A) : ∀ x, A x := decomp p

theorem beta {A : Type 1 → Type 1} (f : ∀ x, A x) (x : Type 1) : app (lam f) x = f x := rfl

theorem unsound : False :=
  Counterexample.girard pi lam app beta
