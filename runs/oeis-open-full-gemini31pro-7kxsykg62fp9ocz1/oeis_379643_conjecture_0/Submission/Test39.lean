import Submission.Spec

#eval ((Finset.range 20).filter (fun p => p.Prime ∧ p % 8 = 3)).card
#eval ((Finset.range 20).filter (fun p => p.Prime ∧ p % 8 = 7)).card
