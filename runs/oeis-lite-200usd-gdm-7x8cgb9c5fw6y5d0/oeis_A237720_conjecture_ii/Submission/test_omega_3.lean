import FormalConjectures.Util.ProblemImports

open Nat

theorem test (n p S : Nat)
    (h_cond2 : p = 2 → n ≤ 193)
    (h_cond3 : p = 3 → n ≤ 192)
    (h_cond5 : p = 5 → n ≤ 191)
    (h_cond6 : p = 7 → n ≤ 190)
    (h_cond7 : p = 11 → n ≤ 189)
    (h_cond8 : p = 13 → n ≤ 188)
    (h_cond9 : p = 17 → n ≤ 187)
    (h_cond10 : p = 19 → n ≤ 186)
    (h_cond11 : p = 23 → n ≤ 185)
    (h_cond12 : p = 29 → n ≤ 184)
    (h_cond13 : p = 31 → n ≤ 183)
    (h_cond14 : p = 37 → n ≤ 182)
    (hS_ge18 : S ≥ 18)
    (hsq : n + 1 + p = S * S)
    (hc : ¬ p ≥ 41) : False := by
  have : p ≤ 40 := by omega
  interval_cases p
  
