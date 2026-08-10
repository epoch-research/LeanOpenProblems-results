inductive Bad (α : Prop) : Type
  | mk : (α → Bad α) → Bad α

-- Let's define a custom SizeOf instance where the size is always 0!
instance : SizeOf (Bad α) where
  sizeOf _ := 0
