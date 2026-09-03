import Submission.Shared47Data
namespace Erdos7Shared47Rows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem stage43_valid : Valid stage43 stage47.F := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k hk
  change k ∈ [1, 24, (1764/43 : ℚ), (77616/1849 : ℚ), (3339252/79507 : ℚ), (143589600/3418801 : ℚ)] at hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  all_goals intro n hn
  all_goals have hn' : n < 24 := List.mem_range.mp hn
  all_goals interval_cases n <;> decide +kernel
#print axioms stage43_valid

end Erdos7Shared47Rows
