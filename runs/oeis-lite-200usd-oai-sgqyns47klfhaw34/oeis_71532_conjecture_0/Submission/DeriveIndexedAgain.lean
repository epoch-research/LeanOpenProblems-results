import FormalConjectures.Util.ProblemImports

inductive BadIdx : Prop → Type
| intro : BadIdx True
  deriving Nonempty

#check BadIdx.instNonempty
#synth Nonempty (BadIdx False)

-- If inhabited, eliminate false-indexed value.
def noBadFalse (x : BadIdx False) : False := by cases x

theorem badFalse : False := noBadFalse (Classical.choice (inferInstance : Nonempty (BadIdx False)))
#print axioms badFalse
