import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0

def M : ℕ := 1194649

def loop_fuel (fuel k : ℕ) (f fact : ℤ) : ℤ :=
  match fuel with
  | 0 => f
  | fuel' + 1 =>
      let k' := k + 1
      let fact' := (fact * k') % (M : ℤ)
      let f' := (k' * f + (if k' % 2 = 0 then (1:ℤ) else -1) * fact) % (M : ℤ)
      loop_fuel fuel' k' f' fact'

def F_fast_mod_fuel (n : ℕ) : ℤ :=
  if n < 2 then 0 else loop_fuel (n - 1) 1 0 1

theorem test : F_fast_mod_fuel 200000 = 0 := by decide
