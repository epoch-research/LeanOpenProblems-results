import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0
  let rec find_min_m (m : ℕ) : ℕ :=
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m (m + 1)
    termination_by n + 1 - m
  find_min_m 1

#eval (List.range 50).map (fun n => (n, a n))
