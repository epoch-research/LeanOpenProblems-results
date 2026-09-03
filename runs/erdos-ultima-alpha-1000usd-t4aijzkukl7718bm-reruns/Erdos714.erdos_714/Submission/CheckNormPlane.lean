import Submission.BinaryLift
#check Module.Finite.of_finite
#check Module.Finite.of_finite_type
#check FiniteDimensional.of_finrank_pos
#check trace_eq_sum_automorphisms
example {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype E] : FiniteDimensional F E := inferInstance
