import FormalConjectures.Util.ProblemImports

inductive TwoProofs : Prop where
| left : TwoProofs
| right : TwoProofs

#check TwoProofs.noConfusion
#print TwoProofs.noConfusion
#check proof_irrel TwoProofs.left TwoProofs.right

example : TwoProofs.left = TwoProofs.right := proof_irrel _ _

example : False := by
  have h : TwoProofs.left = TwoProofs.right := proof_irrel _ _
  exact TwoProofs.noConfusion h
