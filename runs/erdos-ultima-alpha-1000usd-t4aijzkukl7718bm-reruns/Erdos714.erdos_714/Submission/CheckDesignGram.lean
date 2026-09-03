import FormalConjecturesUtil
/-! API checks for exact-design Gram matrices. -/
#check Matrix.PosDef.smul
#check Matrix.PosSemidef.smul
#check Matrix.PosDef.one
#check Matrix.posSemidef_conjTranspose_mul_self
#check Matrix.PosSemidef.conjTranspose_mul_mul_same
#check Matrix.PosDef.add_posSemidef
#check Matrix.PosDef.isUnit
#check Matrix.rank_of_isUnit
#check Matrix.rank_le_card_width
#check Matrix.rank_le_card_height
#check Matrix.rank_transpose_mul_self
#check Finset.eq_of_subset_of_card_le
#check Finset.card_sdiff
#check Fintype.card_subtype_compl
#check Matrix.one_apply
#check Matrix.conjTranspose_eq_transpose_of_trivial
