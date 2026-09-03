import FormalConjecturesUtil
import Submission.DiscardedMatchingCriterion
/-! Scratch checks for the finite target-max matching obstruction. -/
#check Fintype.card_le_of_injective
#check Finset.card_le_card_of_injective
#print Erdos371DiscardedMatchingCriterion.P
#print Nat.maxPrimeFac
#reduce Nat.maxPrimeFac 49729
example : Nat.maxPrimeFac (5*9946-1) < Nat.maxPrimeFac 9946 := by decide +kernel
