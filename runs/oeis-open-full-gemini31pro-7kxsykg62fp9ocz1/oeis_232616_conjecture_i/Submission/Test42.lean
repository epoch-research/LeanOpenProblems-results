import Mathlib

def step (n v : ℕ) (state : ℕ × ℕ × Bool) : ℕ × ℕ × Bool :=
  let k := state.1
  let pow2 := state.2.1
  let found := state.2.2
  if found then state
  else
    let val := if pow2 < k % n then pow2 + n - k % n else pow2 - k % n
    if val == v then (k + 1, (pow2 * 2) % n, true)
    else (k + 1, (pow2 * 2) % n, false)

def step10 (n v : ℕ) (s : ℕ × ℕ × Bool) : ℕ × ℕ × Bool :=
  step n v (step n v (step n v (step n v (step n v
  (step n v (step n v (step n v (step n v (step n v s)))))))))

def step100 (n v : ℕ) (s : ℕ × ℕ × Bool) : ℕ × ℕ × Bool :=
  step10 n v (step10 n v (step10 n v (step10 n v (step10 n v
  (step10 n v (step10 n v (step10 n v (step10 n v (step10 n v s)))))))))

def step1000 (n v : ℕ) (s : ℕ × ℕ × Bool) : ℕ × ℕ × Bool :=
  step100 n v (step100 n v (step100 n v (step100 n v (step100 n v
  (step100 n v (step100 n v (step100 n v (step100 n v (step100 n v s)))))))))

def runChunks (n v : ℕ) : ℕ → ℕ × ℕ × Bool → ℕ × ℕ × Bool
  | 0, s => s
  | fuel + 1, s => runChunks n v fuel (step1000 n v s)

set_option maxHeartbeats 20000000

lemma test_runChunks : (runChunks 550172 13573 16331 (1, 2 % 550172, false)).2.2 = false := by
  decide
