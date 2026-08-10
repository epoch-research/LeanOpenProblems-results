import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def checkAt (i : ℕ) : Bool := (i+1) > i

def pow2 : ℕ → ℕ
| 0 => 1
| d+1 => 2 * pow2 d

def loopTree (depth lo limit : ℕ) : Bool :=
  match depth with
  | 0 => if lo < limit then checkAt lo else true
  | d+1 => loopTree d lo limit && loopTree d (lo + pow2 d) limit

theorem bench : loopTree 17 0 100000 = true := by decide
#print axioms bench
