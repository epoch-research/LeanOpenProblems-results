import FormalConjectures.Util.ProblemImports

open Finset Nat

-- State: (c1, c2, acc)
def State := ℕ × ℕ × ℕ

def step_1 (n : ℕ) (k : ℕ) (s : State) : State :=
  let (c1, c2, acc) := s
  if k < n then
    (c1 * (n - k) / (k + 1), c2 * (n + k) / (k + 1), acc + c1^2 * c2^2)
  else
    s

def run_tree_aux (n : ℕ) : ℕ → ℕ → ℕ → State → State
  | 0, a, len, s => s
  | d + 1, a, 0, s => s
  | d + 1, a, 1, s => step_1 n a s
  | d + 1, a, len, s =>
    let half := len / 2
    let (c1', c2', acc') := run_tree_aux n d a half s
    run_tree_aux n d (a + half) (len - half) (c1', c2', acc')

def run_tree (n : ℕ) : ℕ :=
  let (_, _, acc) := run_tree_aux n 20 0 n (1, 1, 0)
  acc

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

theorem test_16807 : run_tree 16807 % 7^25 = 1012908569057404849376 := by
  decide






















