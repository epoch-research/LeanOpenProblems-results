import Submission.BinaryZeroSpanExplore
#check LinearMap.proj
#check LinearMap.pi
#check Module.Dual.eval_apply
#check Module.evalEquiv_apply
#check Module.evalEquiv_toLinearMap
#check Nat.ofDigits_add
#check List.ofFn_succ
#check Nat.ofDigits_cons
#check Finset.card_le_card_of_injOn
#check Submodule.mem_dualCoannihilator
#check Subspace.finrank_add_finrank_dualCoannihilator_eq
#check Module.Finite.fintype
example {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2)) : FiniteDimensional (ZMod 2) C := inferInstance
example {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2)) : Fintype C := inferInstance
