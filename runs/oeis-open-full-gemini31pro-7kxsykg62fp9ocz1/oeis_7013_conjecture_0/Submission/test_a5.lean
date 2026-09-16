import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Nat.recOn n 2 fun _ a_n => 2 ^ a_n - 1

lemma a_0 : a 0 = 2 := rfl
lemma a_1 : a 1 = 3 := rfl
lemma a_2 : a 2 = 7 := rfl
lemma a_3 : a 3 = 127 := rfl
lemma a_4 : a 4 = 170141183460469231731687303715884105727 := rfl
lemma a_5 : a 5 = 2 ^ 170141183460469231731687303715884105727 - 1 := rfl
