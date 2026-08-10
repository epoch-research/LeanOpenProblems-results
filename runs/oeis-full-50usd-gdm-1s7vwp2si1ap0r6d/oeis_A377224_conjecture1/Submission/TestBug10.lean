inductive Bad : Type where
  | mk : (Prop → Bad) → Bad

def pi : Bad → Prop
  | .mk f => ∃ (P : Prop), ¬ (pi (f P))

def g : Bad → Bad
  | .mk f => g (f (pi (.mk f)))
