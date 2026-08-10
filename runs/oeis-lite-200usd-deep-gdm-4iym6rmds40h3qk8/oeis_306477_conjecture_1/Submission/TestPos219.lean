def pi (A : Prop → Prop) : Prop := ∀ x : Prop, A x
def lam {A : Prop → Prop} (f : ∀ x, A x) : pi A := f
def app {A} (f : pi A) (x) : A x := f x
theorem beta {A : Prop → Prop} (f : ∀ x, A x) (x) : app (lam f) x = f x := rfl

theorem girard_prop : False := by
  let F (X : Prop) : Prop := (X → X) → X
  let U : Prop := pi F
  let G (T : U) (X : Prop) : F X := fun f => f (f (app T X f)) -- wait, we need to adapt G
  sorry
