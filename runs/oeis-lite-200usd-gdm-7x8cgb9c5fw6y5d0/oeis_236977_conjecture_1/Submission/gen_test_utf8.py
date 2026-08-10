import FormalConjectures.Util.ProblemImports

def s : String := "a" * 1000000 + "b"

theorem test_utf8 : s.get 1000000 = 'b' := by
  decide
