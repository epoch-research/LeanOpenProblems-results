inductive Unsound : Prop
| mk : (Prop → Unsound) → Unsound
| base : Unsound

abbrev U := Unsound

def decomp : U → Prop → U
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f

def lam (f : Prop → U) : U := Unsound.mk f

def U_to_Prop : U → Prop → Prop
| Unsound.base, _ => False
| Unsound.mk f, p => ¬ (U_to_Prop (f p) p)
