import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 200000

open Matrix

def N : Nat := 201886 * 3 ^ 39101 - 1
def inv5 : Nat := (2*N + 1) / 5

noncomputable def G : Matrix (Fin 2) (Fin 2) (ZMod N) := !![-(inv5 : ZMod N) - 1, 5 * (-(inv5 : ZMod N)); -(inv5 : ZMod N), -1]
-- matrix of multiplication by gamma on basis (alpha,1)? maybe not important for norm_num test

theorem test_pow_matrix : G ^ 1000 = G ^ 1000 := by
  norm_num [G]
