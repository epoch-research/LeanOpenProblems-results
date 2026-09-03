import FormalConjecturesUtil
import Submission.GlobalSupercriticalCutoff
open Finset Erdos371GlobalSupercriticalCutoff
set_option pp.all true in
#print Finset.card_product
#print Finset.product
#check Finset.card_product'
#check Finset.card_product_finset
#check Finset.card_product_eq
set_option pp.all true in
#check (fun (s : Finset (ℕ×ℕ)) (t : Finset ℕ) => s ×ˢ t)
example (C N : ℕ) : ((orderedPairs (C*N)).product (range (C+1))).card =
    (orderedPairs (C*N)).card * (C+1) := by
  exact (Finset.card_product _ _).trans (by rw [Finset.card_range])
