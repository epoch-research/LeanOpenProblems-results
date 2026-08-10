import Submission.Spec

#check (inferInstance : Decidable ((∀ n L, is_maximal_run 0 n L → (L = 4 ∨ L = 5)) ∧
  (∀ n L, is_maximal_run 1 n L → (L = 3 ∨ L = 4))))
