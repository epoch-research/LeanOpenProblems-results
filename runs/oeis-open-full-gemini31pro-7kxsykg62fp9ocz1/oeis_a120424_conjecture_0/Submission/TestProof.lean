import Mathlib

lemma odd_step_C_ge_91 (F C : ℤ) (hV : F - C.natAbs ≥ 91) (hC_odd : C % 2 ≠ 0) :
  let C_next := F - C
  C_next ≥ 91 := by
  intro C_next
  have h1 : (C.natAbs : ℤ) = if C ≥ 0 then C else -C := by
    split
    · exact Int.natAbs_of_nonneg ‹_›
    · exact Int.ofNat_natAbs_of_nonpos (by omega)
  omega
