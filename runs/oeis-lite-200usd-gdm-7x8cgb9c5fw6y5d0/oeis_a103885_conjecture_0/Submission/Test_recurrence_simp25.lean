import FormalConjectures.Util.ProblemImports

def A103885 : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 16
  | 3 => 146
  | 4 => 1408
  | 5 => 14002
  | n + 1 =>
    if n < 5 then 0 -- actually this branch is never hit because 0 to 5 are handled above, but it helps Lean understand
    else
      let c0 := 220 * n^4 - 136 * n^2 + 12
      let cm := (2 * n - 1) * (2 * n - 2) * (5 * n^2 + 5 * n + 1)
      let cp := (2 * n + 1) * (2 * n + 2) * (5 * n^2 - 5 * n + 1)
      (c0 * A103885 n + cm * A103885 (n - 1)) / cp

#eval A103885 0
#eval A103885 1
#eval A103885 2
#eval A103885 3
#eval A103885 4
#eval A103885 5
#eval A103885 6
