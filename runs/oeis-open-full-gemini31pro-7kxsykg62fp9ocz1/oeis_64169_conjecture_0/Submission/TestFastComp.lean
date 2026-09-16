import FormalConjectures.Util.ProblemImports

def loop (n : ℕ) : ℕ :=
  Id.run do
    let mut s : ℕ := 0
    for i in [1:n+1] do
      s := (s + i) % 12345
    return s

lemma test : loop 283686649 = 2650 := by
  native_decide
