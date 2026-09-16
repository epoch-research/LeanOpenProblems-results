import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def M : ℕ := 1194649
def M_int : ℤ := 1194649

def loop_inner (fuel k : ℕ) (f fact : ℤ) : ℤ × ℤ :=
  match fuel with
  | 0 => (f, fact)
  | fuel' + 1 =>
      let k' := k + 1
      let fact' := (fact * k') % M_int
      let f' := (k' * f + (if k' % 2 = 0 then (1:ℤ) else -1) * fact) % M_int
      loop_inner fuel' k' f' fact'

def loop_outer (fuel chunks : ℕ) (k : ℕ) (f fact : ℤ) : ℤ :=
  match chunks with
  | 0 => (loop_inner fuel k f fact).1
  | chunks' + 1 =>
      let (f', fact') := loop_inner 1000 k f fact
      loop_outer fuel chunks' (k + 1000) f' fact'

def F_fast_chunk (n : ℕ) : ℤ :=
  if n < 2 then 0 else
    let total := n - 1
    let chunks := total / 1000
    let rem := total % 1000
    loop_outer rem chunks 1 0 1

theorem test : F_fast_chunk 200000 = 0 := by decide
