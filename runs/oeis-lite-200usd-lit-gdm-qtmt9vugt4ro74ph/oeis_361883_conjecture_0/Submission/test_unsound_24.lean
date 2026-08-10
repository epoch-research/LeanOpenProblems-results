inductive BadProp : Prop → Prop
  | mk1 {p : Prop} : p → BadProp p
  | mk2 {p : Prop} : BadProp p → BadProp (p → False)
