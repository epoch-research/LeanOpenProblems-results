inductive Bad (F : Type → Type) : Type where
  | mk : F (Bad F) → Bad F
