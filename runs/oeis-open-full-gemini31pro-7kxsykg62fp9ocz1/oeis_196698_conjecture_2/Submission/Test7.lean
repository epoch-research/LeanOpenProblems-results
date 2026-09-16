import Mathlib

#check fun (n : ℕ) => (Finset.range n).biUnion (fun k => {k, k+1})
