inductive V : Prop
| mk : (Prop → V) → V

def decomp : V → (Prop → V)
| V.mk f => f

theorem V_eq : V = (Prop → V) := by
  apply propext
  constructor
  · exact decomp
  · exact V.mk
