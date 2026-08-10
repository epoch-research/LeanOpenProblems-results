inductive BadProp : Prop → Prop
  | mk1 {p : Prop} : p → BadProp p
  | mk2 {p : Prop} : BadProp p → BadProp (p → False)

def val : (p : Prop) → BadProp p → Prop
  | p, BadProp.mk1 g => (p → False) → False
  | p, BadProp.mk2 z => val (p → False) z

def prove_val : (p : Prop) → (t : BadProp p) → val p t
  | p, BadProp.mk1 g => fun h => h g
  | p, BadProp.mk2 z => prove_val (p → False) z
