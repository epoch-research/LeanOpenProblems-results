import Submission.Shared47Data
namespace Erdos7Shared47Rows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem stage31_valid : Valid stage31 stage37.F := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k hk
  change k ∈ [1, 12, 16, (900/31 : ℚ), (28800/961 : ℚ), (893700/29791 : ℚ), (27705600/923521 : ℚ)] at hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  all_goals intro n hn
  all_goals have hn' : n < 24 := List.mem_range.mp hn
  all_goals interval_cases n <;> decide +kernel
#print axioms stage31_valid

end Erdos7Shared47Rows
