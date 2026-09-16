import Submission.Spec
open PowerSeries

theorem den_inv : ((1 - X) * (1 - X ^ 8) * (1 - X ^ 12) * (1 - X ^ 24) : PQS)⁻¹ = 0 := by
  -- is there a `Inv` instance that maps non-units to 0?
  -- Wait, for `PowerSeries`, `Inv` is only defined if the constant term is invertible.
  -- But Mathlib's `Inv` might be defined differently.
  sorry
