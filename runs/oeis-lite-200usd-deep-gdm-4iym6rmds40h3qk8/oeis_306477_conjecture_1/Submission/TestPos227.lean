open Classical

def Set_prop (X : Prop) : Prop := (X → False) → False

def pi (A : Prop → Prop) : Prop := ∀ x : Prop, A x
def lam {A : Prop → Prop} (f : ∀ x, A x) : pi A := f
def app {A} (f : pi A) (x) : A x := f x
theorem beta {A : Prop → Prop} (f : ∀ x, A x) (x) : app (lam f) x = f x := rfl

theorem girard_prop : False := by
  let F (X : Prop) : Prop := (Set_prop (Set_prop X) → X) → Set_prop (Set_prop X)
  let U : Prop := pi F
  let G (T : Set_prop (Set_prop U)) (X : Prop) : F X := fun f =>
    fun (h : Set_prop X → False) =>
      -- we want to return False.
      -- We have:
      --   T : Set_prop (Set_prop U) = ((¬¬ U → False) → False)
      --   X : Prop
      --   f : Set_prop (Set_prop X) → X
      --   h : ¬¬ X → False
      sorry
  sorry
