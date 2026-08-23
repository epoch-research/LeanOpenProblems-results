import FormalConjectures.Util.ProblemImports

open Nat Function

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then (3 * k) / 2
  else if k % 4 = 1 then (3 * k + 1) / 4
  else (3 * k - 1) / 4

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def n500 : ℕ := 100756188284683804

lemma chunk500from : ∀ k : Fin 500, A006368_map^[k.val] n500 ≠ 64 := by decide
#print axioms chunk500from
