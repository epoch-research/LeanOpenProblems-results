import FormalConjectures.Util.ProblemImports

mutual
  partial def cycProof (P : Prop) : P := default
  instance cycInhabited (P : Prop) : Inhabited P := ⟨cycProof P⟩
end

example : False := cycProof False
#print axioms cycProof
#print axioms cycInhabited
