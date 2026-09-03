import FormalConjecturesUtil
import Submission.PrimeDiscrepancy
#print Nat.maxPrimeFac
#print Erdos371PrimeDiscrepancy.P
set_option pp.all true in
#check ((Finset.range 99).filter (fun n => Erdos371PrimeDiscrepancy.P n = 11))
example : Nat.maxPrimeFac 98 = 7 := by decide +kernel
example : (Finset.range 5).filter (fun n => Nat.maxPrimeFac n = 3) = {3} := by decide +kernel
