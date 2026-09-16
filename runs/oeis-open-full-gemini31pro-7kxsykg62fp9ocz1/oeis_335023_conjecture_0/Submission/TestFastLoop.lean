import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0

def F_fast (n : ℕ) : ℤ :=
  let rec loop (k : ℕ) (f : ℤ) (fact : ℤ) : ℤ × ℤ :=
    if h : k < n then
      let k' := k + 1
      let fact' := fact * k'
      let f' := k' * f + (if k' % 2 = 0 then (1:ℤ) else -1) * fact
      loop k' f' fact'
    else (f, fact)
  decreasing_by sorry
  if n < 2 then 0 else (loop 1 0 1).1

#eval F_fast 1000
