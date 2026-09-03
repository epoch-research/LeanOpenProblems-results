import Submission.TestNearbyGenericData
/-! Development diagnostic. -/
namespace Erdos970.GapAverages.NearbyExample
example : True := by
  have hc := card_filter_range_blocks3 (fun a => CyclicSieve.natCount primes 7 a = 0) 100 150 15
  exact True.intro
end Erdos970.GapAverages.NearbyExample
