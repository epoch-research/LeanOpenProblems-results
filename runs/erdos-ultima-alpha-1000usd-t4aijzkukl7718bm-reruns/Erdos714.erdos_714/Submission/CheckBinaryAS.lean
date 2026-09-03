import FormalConjecturesUtil
/-! Scratch declarations. -/
variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
#synth Algebra (ZMod 2) F
#synth FiniteDimensional (ZMod 2) F
#synth Algebra.IsSeparable (ZMod 2) F
#check ZMod.algebra
#check ZMod.castHom
#check AddSubgroup.card_eq_iff_eq_of_le
#check Nat.card_pos
#check AddSubgroup.card_bot
#check AddSubgroup.card_top
#check AddMonoidHom.range_eq_top
#check AddSubgroup.eq_of_le_of_card_ge
#check Finset.card_image_le
#check Fintype.card_subtype_iff
#check AddSubgroup.card_le_card
#check Submodule.eq_of_le_of_finrank_eq
#check LinearMap.rank_range_add_rank_ker
#check LinearMap.finrank_range_add_finrank_ker
#check Polynomial.card_roots
#check Finset.card_le_card
#check Finset.eq_of_subset_of_card_le
#check AddSubgroup.toFinset_card
#check Finset.card_congr
#check Fintype.card_congr
#check AddSubgroup.mem_carrier
#check AddMonoidHom.mem_ker
#check FiniteField.algebraMap_norm_eq_pow
