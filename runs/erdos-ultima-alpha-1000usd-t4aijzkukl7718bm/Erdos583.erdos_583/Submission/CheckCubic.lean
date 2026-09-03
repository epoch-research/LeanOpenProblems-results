import Submission.ButterflyContiguous
/-! API check. -/
open SimpleGraph Erdos583Work
#check Walk.IsPath.take
#check Walk.IsPath.drop
#check Walk.IsPath.of_append_left
#check Walk.take_length
#check Walk.append_take_drop_eq
#check Set.iUnion_singleton_eq_range
#check Walk.IsPath.mk'
#check Walk.IsCycle.mk
#check Set.ncard_range_of_injective
#check TriangleAbsorption.disjoint_of_cover_length
