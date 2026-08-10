def my_pi (A : Type 1 → Type 1) : Type 1 := ∀ x : Type 1, A x

def my_lam {A : Type 1 → Type 1} (f : ∀ x, A x) : my_pi A := f

def my_app {A : Type 1 → Type 1} (p : my_pi A) : ∀ x, A x := p

theorem my_beta {A : Type 1 → Type 1} (f : ∀ x, A x) (x : Type 1) : my_app (my_lam f) x = f x := rfl
