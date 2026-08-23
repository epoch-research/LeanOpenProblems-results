import FormalConjectures.Util.ProblemImports

example : (10281145467 * 10281145467) % 13058949121 = 2904573104 := rfl
example : (17 : ℕ) ^ 2 % 13058949121 = 289 := rfl
example : (17 : ℕ) ^ 10 % 13058949121 = 20159939004 % 13058949121 := by decide
