import Submission.Spec
open Polynomial

theorem const_is_unit (c : ℚ) (hc : c ≠ 0) : IsUnit (C c) := by
  exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
