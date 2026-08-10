inductive V : Prop
| mk : (Prop → V) → V

def decomp : V → (Prop → V)
| V.mk f => f

def root_V : V := V.mk (fun h => False.elim h)
