def Set (X : Type 0) : Prop := X → False

def Set_Prop (X : Type 0) : Prop := PLift (Set X) → False

def F (X : Type 0) : Prop := (Set_Prop X → X) → Set_Prop X

inductive Unsound : Prop
| mk : (∀ X : Type 0, F X) → Unsound

abbrev U := Unsound

def decomp : U → (∀ X : Type 0, F X)
| Unsound.mk f => f

def lam (f : ∀ X : Type 0, F X) : U := Unsound.mk f

def app (u : U) (X : Type 0) : F X := decomp u X

theorem beta (f : ∀ X : Type 0, F X) (X : Type 0) : app (lam f) X = f X := rfl

abbrev U0 := PLift U

noncomputable def G (T : Set_Prop U0) (X : Type 0) : F X :=
  fun f => fun p => T (PLift.up (fun x => p.down (f (PLift.up (app (PLift.down x) X f)))))

noncomputable def τ (T : Set_Prop U0) : U := lam (G T)

noncomputable def σ (S : U0) : Set_Prop U0 :=
  app (PLift.down S) U0 (fun f => PLift.down (f (PLift.up (fun x => PLift.down (app (PLift.down x) U0 f))))) -- wait, we need to match the type of f

theorem στ (s : PLift (Set U0)) (S : Set_Prop U0) :
  σ (PLift.up (τ S)) s ↔ S (fun x => s.down (PLift.up (τ (σ (PLift.up x))))) := sorry
