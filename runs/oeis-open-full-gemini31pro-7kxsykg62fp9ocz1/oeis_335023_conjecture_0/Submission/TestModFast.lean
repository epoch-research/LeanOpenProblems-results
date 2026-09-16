import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 2000000

def M : ℤ := (1093 : ℤ) ^ 1092

def F_loop (fuel k : ℕ) (f fact : ℤ) : ℤ × ℤ :=
  match fuel with
  | 0 => (f, fact)
  | fuel' + 1 =>
      let k' := k + 1
      let fact' := (fact * k') % M
      let f' := (k' * f + (if k' % 2 = 0 then (1:ℤ) else -1) * fact) % M
      F_loop fuel' k' f' fact'

def F_fast (n : ℕ) : ℤ :=
  if n < 2 then 0 else (F_loop (n - 1) 1 0 1).1

theorem test : F_fast 10000 = 0 := by decide
