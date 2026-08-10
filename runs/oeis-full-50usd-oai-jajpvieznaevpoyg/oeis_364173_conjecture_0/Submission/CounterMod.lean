import FormalConjectures.Util.ProblemImports
example : ¬ ((1:ℤ) ≡ 2 [ZMOD ((5:ℤ) ^ (3*1))]) := by native_decide
#eval ((5:ℤ) ^ (3*1))
