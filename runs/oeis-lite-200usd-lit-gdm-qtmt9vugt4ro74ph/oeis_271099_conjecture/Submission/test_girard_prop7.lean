def my_pi (A : Type → Type) : Type 1 := ∀ x, A x
def my_lam {A : Type → Type} (f : ∀ x, A x) : my_pi A := f
def my_app {A} (f : my_pi A) (x : Type) : A x := f x
def my_beta {A : Type → Type} (f : ∀ x, A x) (x : Type) : my_app (my_lam f) x = f x := rfl

def F (X : Type) : Type := (((X → Prop) → Prop) → X) → ((X → Prop) → Prop)
def U : Type 1 := my_pi F

def G (T : (U → Prop) → Prop) (X : Type) : F X :=
  fun f p => T (fun x => p (f (my_app x X f)))

def τ (T : (U → Prop) → Prop) : U := my_lam (G T)
def σ (S : U) : (U → Prop) → Prop := my_app S U τ
