import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 2000000

def M : ℕ := 1194649

def loop_strict (fuel k : ℕ) (f fact : ℤ) : ℤ :=
  match fuel with
  | 0 => f
  | fuel' + 1 =>
      let k' := k + 1
      let fact' := (fact * k') % (M : ℤ)
      let f' := (k' * f + (if k' % 2 = 0 then (1:ℤ) else -1) * fact) % (M : ℤ)
      if f' = f' then loop_strict fuel' k' f' fact' else 0

def F_fast_strict (n : ℕ) : ℤ :=
  if n < 2 then 0 else loop_strict (n - 1) 1 0 1

theorem test : F_fast_strict 200000 = 0 := by decide
