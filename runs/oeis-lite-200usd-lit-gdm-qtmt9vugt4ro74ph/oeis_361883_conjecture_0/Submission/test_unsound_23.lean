inductive BadProp : Prop
  | mk : (BadProp → False) → BadProp
