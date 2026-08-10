import FormalConjectures.Util.ProblemImports

example : (Or.inl True.intro : True ∨ True) = Or.inr True.intro := proof_irrel _ _

example : False := by
  have h : (Or.inl True.intro : True ∨ True) = Or.inr True.intro := proof_irrel _ _
  cases h

example : False := by
  have h : (Exists.intro 0 True.intro : ∃ n : Nat, True) = Exists.intro 1 True.intro := proof_irrel _ _
  cases h

#print Or.noConfusion
#check Or.noConfusion
#print Exists.noConfusion
#check Exists.noConfusion
