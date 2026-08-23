import FormalConjectures.Util.ProblemImports

open Nat Function

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then (3 * k) / 2
  else if k % 4 = 1 then (3 * k + 1) / 4
  else (3 * k - 1) / 4

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def n4000 : ℕ := 235383608278701712744229028048507925539414759591396077471566361578588280512972304682439468419

lemma chunk : ∀ k : Fin 500, A006368_map^[k.val] n4000 ≠ 64 := by decide
#print axioms chunk
