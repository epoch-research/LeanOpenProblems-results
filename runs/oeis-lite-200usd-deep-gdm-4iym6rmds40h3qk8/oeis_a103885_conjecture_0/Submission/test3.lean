import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Finset

def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

theorem a_68_eq : A103885 68 = 2599200093830976389575137274817233400171336491307633017336968343653760 := by decide
