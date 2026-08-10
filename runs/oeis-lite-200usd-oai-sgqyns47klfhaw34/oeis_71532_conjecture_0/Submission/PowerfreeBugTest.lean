import FormalConjectures.Util.ProblemImports

#check Powerfree.of_le
#check Powerfree.of_dvd
#check not_powerfree_zero
#check powerfree_two

-- concrete tests
#eval decide (Powerfree 2 (4:ℕ))
#eval decide (Powerfree 3 (4:ℕ))
#eval decide (Powerfree 1 (4:ℕ))

example : False := by
  -- try Powerfree.of_dvd with r=4,m=4,k=3: 4 is 3-powerfree? true; get 4 powerfree? same
  norm_num

#print axioms Powerfree.of_dvd
