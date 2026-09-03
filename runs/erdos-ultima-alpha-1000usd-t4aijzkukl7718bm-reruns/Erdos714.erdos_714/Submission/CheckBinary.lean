import FormalConjecturesUtil
open scoped CharTwo
#check CharTwo.add_eq_zero
#check CharTwo.add_self_eq_zero
#check CharTwo.neg_eq
#check CharTwo.add_cancel_left
#check Bool.false_ne_true
set_option trace.Meta.Tactic.simp.rewrite true in
example {G : Type*} [Ring G] [CharP G 2] {u v : G} (h : u ≠ v) : u + v ≠ 0 := by
  intro h0
  exact h (CharTwo.add_eq_zero.mp h0)
