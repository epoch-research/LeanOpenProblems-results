import FormalConjectures.Util.ProblemImports

inductive Delay (P : Prop) where
| later : Delay P → Delay P
  deriving Nonempty

#check (inferInstance : Nonempty (Delay False))

def loopDelay (P : Prop) : Delay P := Classical.choice inferInstance

-- no way to extract P? try recursor
#check Delay.rec
