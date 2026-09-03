import FormalConjecturesUtil
#check Module.finrank_span_finset_le_card
#check finrank_span_finset_le_card
#check ZMod.eq_zero_or_eq_one
#check ZMod.eq_one_of_ne_zero
#check Submodule.map_eq_bot_iff_le_ker
#check Submodule.map_le_iff_le_comap
#check Submodule.mem_dualCoannihilator
#check Subspace.finrank_add_finrank_dualCoannihilator_eq
#check Module.evalEquiv_apply
#check LinearMap.ker_le_iff
#check Finset.card_filter_add_card_filter_not
example {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] : Finite (Module.Dual (ZMod 2) V) := inferInstance
