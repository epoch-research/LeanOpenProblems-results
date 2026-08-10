import FormalConjectures.Util.ProblemImports

unsafe def test_unsafe (n : ℕ) : 0 < 1 :=
  test_unsafe n

theorem test_thm (n : ℕ) : 0 < 1 :=
  test_unsafe n
