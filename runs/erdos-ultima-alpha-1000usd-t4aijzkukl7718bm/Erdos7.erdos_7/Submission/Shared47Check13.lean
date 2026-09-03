import Submission.Shared47Data
namespace Erdos7Shared47Rows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem stage13_valid : Valid stage13 stage17.F := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k hk
  change k ∈ [1, 4, (144/13 : ℚ), (2016/169 : ℚ), (26352/2197 : ℚ), (342720/28561 : ℚ)] at hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  all_goals intro n hn
  all_goals have hn' : n < 24 := List.mem_range.mp hn
  all_goals interval_cases n <;> decide +kernel
#print axioms stage13_valid

end Erdos7Shared47Rows
