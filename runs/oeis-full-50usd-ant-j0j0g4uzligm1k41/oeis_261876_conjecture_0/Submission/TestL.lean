import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
example : (List.range 15000).foldl (fun a b => a + (b % 2)) 0 = 7500 := by rfl
