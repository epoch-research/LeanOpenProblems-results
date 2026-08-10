import FormalConjectures.Util.ProblemImports

def test_func (idx : ℕ) : ℕ :=
  match idx with
  | 6000 => 3
  | 6001 => 11
  | 6002 => 11
  | 6003 => 19
  | 6399 => 31
  | _ => 3

lemma test_func_prime (idx : ℕ) : Nat.Prime (test_func idx) := by
  unfold test_func
  split <;> decide
