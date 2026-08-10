inductive pi (A : Type 0 → Type 0) : Type 1
| mk : (∀ x, A x) → pi A

def decomp {A : Type 0 → Type 0} : pi A → (∀ x, A x)
| pi.mk f => f

def lam {A : Type 0 → Type 0} (f : ∀ x, A x) : pi A :=
  pi.mk f

def app {A : Type 0 → Type 0} (p : pi A) : ∀ x, A x :=
  decomp p

theorem beta {A : Type 0 → Type 0} (f : ∀ x, A x) (x : Type 0) : app (lam f) x = f x := rfl
