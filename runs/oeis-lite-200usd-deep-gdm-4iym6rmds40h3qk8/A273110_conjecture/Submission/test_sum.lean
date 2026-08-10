import FormalConjectures.Util.ProblemImports

#check Finset.sum (Finset.range 2) (fun x => x)

theorem test_sum : Finset.sum (Finset.range 2) (fun x => x) = 1 := by rfl
