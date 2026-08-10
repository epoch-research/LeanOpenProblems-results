def sb := (Prop → Prop) → Prop

def g (T : sb) : Prop :=
  ∀ (p : Prop → Prop), (∀ (x : Prop), T (fun _ => x) → p x) → p (∀ (x : Prop), T (fun _ => x) → x)

def f (A : Prop) : sb :=
  fun (p : Prop → Prop) => p A
