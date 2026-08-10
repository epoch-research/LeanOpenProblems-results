def Set (X : Type u) : Type u := X → Prop

def F (X : Type 0) : Type 0 := (Set (Set X) → X) → Set (Set X)

inductive Bad : Type 1
| mk : (∀ X : Type 0, F X) → Bad

def decomp : Bad → (∀ X : Type 0, F X)
| Bad.mk f => f

abbrev U := Bad

def lam (f : ∀ X : Type 0, F X) : U := Bad.mk f

def app (u : U) (X : Type 0) : F X := decomp u X

theorem beta (f : ∀ X : Type 0, F X) (X : Type 0) : app (lam f) X = f X := rfl

theorem girard : False := by
  let G (T : Set (Set U)) (X : Type 0) : F X := fun f => fun p => T (fun x => p (f (app x X f)))
  let τ (T : Set (Set U)) : U := lam (G T)
  let σ (S : U) : Set (Set U) := app S U τ
  -- Wait, app S expects X : Type 0, but U is in Type 1!
  -- So app S U expects U : Type 0, but U : Type 1!
  sorry
