def my_pi (A : Prop → Prop) : Prop := ∀ x : Prop, A x

def my_lam {A : Prop → Prop} (f : ∀ x, A x) : my_pi A := f

def my_app {A : Prop → Prop} (p : my_pi A) : ∀ x, A x := p

theorem my_beta {A : Prop → Prop} (f : ∀ x, A x) (x : Prop) : my_app (my_lam f) x = f x := rfl
