import Submission.Sieve729TenLogic
/-! Benchmark of a packed finite-walk certificate. -/
namespace Erdos952Investigation.Sieve729Ten
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private def word : ℕ := 0xa7a77b777337677677379737ba7677a72767767737337760677b77677a727a7767767aa777677677677677a737760377677a727677a7767aabaaba7aa6a7b776
private theorem certified : check 128 word (0,4) (16,188) = true := by
  decide +kernel
theorem bench128 : graph.Reachable (0,4) (16,188) :=
  (check_sound 128 word (0,4) (16,188) certified).2
#print axioms bench128
end Erdos952Investigation.Sieve729Ten
