inductive Bad : Type 1
| mk1 : ((Bad → Prop) → Prop) → Bad

def decomp : Bad → ((Bad → Prop) → Prop)
| Bad.mk1 f => f
