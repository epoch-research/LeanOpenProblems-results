import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0

def M : ℕ := 1194649

def F_fast_mod (n : ℕ) : ℤ :=
  let rec loop (k : ℕ) (f : ℤ) (fact : ℤ) : ℤ :=
    if h : k < n then
      let k' := k + 1
      let fact' := (fact * k') % (M : ℤ)
      let f' := (k' * f + (if k' % 2 = 0 then (1:ℤ) else -1) * fact) % (M : ℤ)
      have : n - k' < n - k := by omega
      loop k' f' fact'
    else f
  termination_by n - k
  if n < 2 then 0 else loop 1 0 1

#eval! F_fast_mod 200000
