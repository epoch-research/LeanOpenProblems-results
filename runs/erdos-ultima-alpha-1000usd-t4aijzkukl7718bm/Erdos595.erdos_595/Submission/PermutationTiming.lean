import FormalConjecturesUtil
set_option maxHeartbeats 100000000
#check Nat
private theorem pair_permutation : ∀ u v : Fin 4, u ≠ v →
    ∃ e : Fin 4 → Fin 4, Function.Bijective e ∧ e 0 = u ∧ e 1 = v := by
  decide +kernel
#print axioms pair_permutation
