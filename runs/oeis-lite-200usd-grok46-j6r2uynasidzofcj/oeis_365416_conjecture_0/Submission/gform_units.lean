import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 80000
set_option maxHeartbeats 16000000

def step73 : ZMod 73 × ZMod 73 × ZMod 73 → ZMod 73 × ZMod 73 × ZMod 73
  | (a, b, c) => (b, c, 9 * c - 21 * b + a)

def iter73 : ℕ → ZMod 73 × ZMod 73 × ZMod 73 → ZMod 73 × ZMod 73 × ZMod 73
  | 0, s => s
  | n + 1, s => iter73 n (step73 s)

lemma iter73_20 :
    iter73 20 (0, -1, -4) = (step73^[20]) (0, -1, -4) := by
  decide

lemma iter73_50 : True := by
  have h := iter73 50 (0, -1, -4)
  -- force reduction via decide equality to a concrete value
  native_decide -- just to get the value first? skip
  trivial

#eval iter73 50 (0, -1, -4)
#eval iter73 100 (0, -1, -4)
#eval iter73 1801 (0, -1, -4)
