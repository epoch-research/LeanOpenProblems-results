import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def N : Nat := 201886 * 3 ^ 39101 - 1

theorem prime_N : Nat.Prime N := by
  unfold N
  norm_num
#print axioms prime_N
