def pi (A : Prop → Type 0) : Type 0 := ∀ x : Prop, A x

def lam {A : Prop → Type 0} (f : ∀ x, A x) : pi A := f

def app {A : Prop → Type 0} (p : pi A) : ∀ x, A x := p

theorem beta {A : Prop → Type 0} (f : ∀ x, A x) (x : Prop) : app (lam f) x = f x := rfl

def Set (X : Sort u) : Type 0 := X → Prop

def F (X : Prop) : Type 0 := (Set (Set X) → X) → Set (Set X)

theorem girard : False := by
  let U : Type 0 := pi F
  let G (T : Set (Set U)) (X : Prop) : F X := fun f => fun p => T (fun x => p (f (app x X f)))
  let τ (T : Set (Set U)) : U := lam (G T)
  let σ (S : U) : Set (Set U) := app S U τ
  -- Let's see if στ compiles with Iff.rfl!
  have στ : ∀ (s : Set U) (S : Set (Set U)), σ (τ S) s ↔ S (fun x => s (τ (σ x))) := fun s S => Iff.rfl
  sorry
