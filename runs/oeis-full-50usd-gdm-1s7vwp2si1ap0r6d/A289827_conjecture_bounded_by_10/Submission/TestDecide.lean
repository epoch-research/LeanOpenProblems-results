import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

noncomputable def A289827 (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => π (m + n) = π m + π n) n

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem test_range : (List.range 300).all (fun n => decide (A289827 n ≤ 10)) = true := by decide

