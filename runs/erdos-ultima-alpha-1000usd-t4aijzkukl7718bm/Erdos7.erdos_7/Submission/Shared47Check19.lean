import Submission.Shared47Data
namespace Erdos7Shared47Rows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem stage19_valid : Valid stage19 stage23.F := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k hk
  change k ∈ [1, 8, (324/19 : ℚ), (6480/361 : ℚ), (123444/6859 : ℚ), (2345760/130321 : ℚ)] at hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  all_goals intro n hn
  all_goals have hn' : n < 24 := List.mem_range.mp hn
  all_goals interval_cases n <;> decide +kernel
#print axioms stage19_valid

end Erdos7Shared47Rows
