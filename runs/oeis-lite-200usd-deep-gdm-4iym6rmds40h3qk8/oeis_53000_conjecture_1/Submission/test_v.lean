inductive V : Prop
| mk : (Prop → V) → V

def decomp : V → (Prop → V)
| V.mk f => f
