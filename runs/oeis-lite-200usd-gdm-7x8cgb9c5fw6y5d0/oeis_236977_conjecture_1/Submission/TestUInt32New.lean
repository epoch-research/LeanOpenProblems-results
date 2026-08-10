import FormalConjectures.Util.ProblemImports

def test_val : UInt32 := 1000000000

theorem test_decide : test_val % 3 = 1 := by
  decide
