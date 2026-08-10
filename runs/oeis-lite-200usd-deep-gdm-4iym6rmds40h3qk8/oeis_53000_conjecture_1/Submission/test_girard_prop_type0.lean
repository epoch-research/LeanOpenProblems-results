def pi (A : Prop → Type 0) : Type 0 := ∀ x : Prop, A x

def lam {A : Prop → Type 0} (f : ∀ x, A x) : pi A := f

def app {A : Prop → Type 0} (p : pi A) : ∀ x, A x := p

theorem beta {A : Prop → Type 0} (f : ∀ x, A x) (x : Prop) : app (lam f) x = f x := rfl

def Set (X : Type 0) : Type 0 := X → Prop

-- Since X : Prop, we want Set_Prop for Prop:
def Set_Prop (X : Prop) : Type 0 := X → Prop

def F (X : Prop) : Type 0 := (Set (Set_Prop X) → X) → Set (Set_Prop X)

theorem girard : False := by
  let U : Type 0 := pi F
  let G (T : Set (Set_Prop U)) (X : Prop) : F X := fun f => fun p => T (fun x => p (f (app x X f)))
  let τ (T : Set (Set_Prop U)) : U := lam (G T)
  let σ (S : U) : Set (Set_Prop U) := app S U τ
  -- We'll check if the rest works
  sorry
