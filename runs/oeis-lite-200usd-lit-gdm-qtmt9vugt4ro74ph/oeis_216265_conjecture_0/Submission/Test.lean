import FormalConjectures.Util.ProblemImports

@[default_instance 200]
instance : SizeOf ℕ where
  sizeOf n := 100 - n

def f (n : ℕ) : False :=
  f (n + 1)
  termination_by n
  decreasing_by
    trace_state
    sorry


































































