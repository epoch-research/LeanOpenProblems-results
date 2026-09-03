import Submission.RightTowerCountableCover
/-! API checks for an auxiliary directed right-adjoint calculation. -/
open Cardinal Ordinal
#check Cardinal.mk_ord_toType
#check Cardinal.mk_Iio_ord_toType
#check Ordinal.isSuccLimit_ord
#check Ordinal.ToType.noMaxOrder
#check Ordinal.isSuccLimit_iff
#check Cardinal.IsRegular.cof_eq
#check Cardinal.mk_coe_iff
#check Cardinal.mk_subtype_le
#check Cardinal.mk_le_of_injective
#check Order.succ_lt_iff
#check Ordinal.ToType.lt_toType
#check Ordinal.ToType.mk
#check Cardinal.mk_toType
#check Ordinal.isSuccLimit_iff_noMaxOrder
example (c : Cardinal) (h : ℵ₀ ≤ c) : NoMaxOrder c.ord.ToType := by
  letI : Fact (IsSuccLimit c.ord) := ⟨Ordinal.isSuccLimit_ord h⟩
  infer_instance
