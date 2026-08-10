import FormalConjectures.Util.ProblemImports

def a_test (n : ℕ) : ℕ := 0

@[extern "some_c_function"]
opaque inst (n : ℕ) : PLift (a_test n ≠ 4)
