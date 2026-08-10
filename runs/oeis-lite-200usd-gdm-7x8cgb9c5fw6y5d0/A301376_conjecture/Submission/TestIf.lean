import FormalConjectures.Util.ProblemImports

def test_if (v : ℕ) : ℕ :=
  if v = 76474351616 then 1871
  else if v = 274877906944 then 3
  else 3

lemma test_if_prime (v : ℕ) : Nat.Prime (test_if v) := by
  unfold test_if
  split_ifs <;> decide
