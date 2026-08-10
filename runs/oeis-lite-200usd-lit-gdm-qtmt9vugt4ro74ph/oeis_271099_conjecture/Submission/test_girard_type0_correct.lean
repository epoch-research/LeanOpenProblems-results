def my_pi (A : Type → Type) : Type 1 := ∀ x, A x
def my_lam {A : Type → Type} (f : ∀ x, A x) : my_pi A := f
def my_app {A} (f : my_pi A) (x : Type) : A x := f x
def my_beta {A : Type → Type} (f : ∀ x, A x) (x : Type) : my_app (my_lam f) x = f x := rfl
