import FormalConjectures.Util.ProblemImports

def loop_test (n : ℕ) : ℕ :=
  Id.run do
    let mut s : ℕ := 0
    for i in [1:n] do
      s := (s + i) % 1000000007
    return s

#eval loop_test 283686649
