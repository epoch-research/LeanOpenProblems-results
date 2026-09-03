import Submission.Work
/-! Check kernel reduction for permutation enumeration. -/
example : ([0,1,2] : List (Fin 3)).permutations'.length=6 := by decide
example : ([0,1,2] : List (Fin 3)).permutations.length=6 := by decide
