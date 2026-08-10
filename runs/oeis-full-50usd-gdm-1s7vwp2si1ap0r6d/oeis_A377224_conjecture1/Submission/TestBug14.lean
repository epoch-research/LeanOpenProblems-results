inductive Bad : Prop where
  | mk : (α : Prop) → (α → Bad) → Bad

def pi (b : Bad) : Prop :=
  match b with
  | Bad.mk α f =>
    ∃ (h : α = (Bad → Prop)),
      let f_cast : (Bad → Prop) → Bad := cast (congrArg (fun X => X → Bad) h) f
      ¬ pi (f_cast pi)
