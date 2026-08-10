open Classical

def Set_prop (X : Prop) : Prop := (X → Prop) → Prop

def pi (A : Prop → Prop) : Prop := ∀ x : Prop, A x
def lam {A : Prop → Prop} (f : ∀ x, A x) : pi A := f
def app {A : Prop → Prop} (f : pi A) (x : Prop) : A x := f x
theorem beta {A : Prop → Prop} (f : ∀ x, A x) (x : Prop) : app (lam f) x = f x := rfl

theorem girard_prop : False := by
  let F (X : Prop) : Prop := (Set_prop (Set_prop X) → X) → Set_prop (Set_prop X)
  let U : Prop := pi F
  let G (T : Set_prop (Set_prop U)) (X : Prop) : F X := fun f => {p : Set_prop X | {x : U | f (app x X f) ∈ p} ∈ T}
  -- Wait, {x : U | ...} is notation for Set, but Set_prop X is (X → Prop) → Prop.
  -- Let's use the explicit lambda notation instead of {x | ...} to avoid Set conflicts.
  sorry
