import FormalConjectures.Util.ProblemImports

open Nat

set_option exponentiation.threshold 25000
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000

def triBits : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    let t := (k + 1) * (k + 2) / 2
    triBits k ||| (2 ^ t)

def addVals (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: vs => (base <<< v) ||| addVals base vs

def qL : List ℕ := [0, 1, 5, 15, 35, 70, 126, 210, 330, 495, 715, 1001, 1365, 1820, 2380, 3060, 3876, 4845, 5985, 7315, 8855, 10626, 12650, 14950, 17550]
def rL : List ℕ := [0, 1, 7, 28, 84, 210, 462, 924, 1716, 3003, 5005, 8008, 12376, 18564]
def sL : List ℕ := [0, 1, 9, 45, 165, 495, 1287, 3003, 6435, 12870]

def covered : ℕ :=
  let t := triBits 199
  let q := addVals t qL
  let r := addVals q rL
  addVals r sL

def mask : ℕ := (2 ^ 20001) - 2

theorem cover20000 : covered &&& mask = mask := by
  decide
