import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- Bit `i` of the `ℕ`-encoded bitset. -/
def bit (s i : ℕ) : Bool := (s >>> i) &&& 1 == 1

/-- Set bit `i`. -/
def setBit (s i : ℕ) : ℕ := s ||| (1 <<< i)

/-- Triangular bits `C(w+2,2)` for `w < W` with value `≤ N`. -/
def triBits (N W : ℕ) : ℕ :=
  (range W).fold (fun w s =>
    let t := (w + 2).choose 2
    if t ≤ N then setBit s t else s) 0

/-- Convolve a bitset with a list of shifts, truncated at `N`. -/
def convBits (s : ℕ) (shifts : List ℕ) (N : ℕ) : ℕ :=
  shifts.foldl (fun acc v =>
    acc ||| ((s <<< v) &&& ((1 <<< (N + 1)) - 1))) 0

def Qlist (N : ℕ) : List ℕ :=
  (range (N + 1)).toList.filterMap fun x =>
    let q := (x + 3).choose 4
    if q ≤ N then some q else none

def Rlist (N : ℕ) : List ℕ :=
  (range (N + 1)).toList.filterMap fun y =>
    let r := (y + 5).choose 6
    if r ≤ N then some r else none

def Slist (N : ℕ) : List ℕ :=
  (range (N + 1)).toList.filterMap fun z =>
    let t := (z + 7).choose 8
    if t ≤ N then some t else none

def allBits (N : ℕ) : ℕ :=
  let t := triBits N (N + 1)
  let q := convBits t (Qlist N) N
  let r := convBits q (Rlist N) N
  convBits r (Slist N) N

def maskFrom1 (N : ℕ) : ℕ := (1 <<< (N + 1)) - 2

lemma test20 : allBits 20 &&& maskFrom1 20 = maskFrom1 20 := by native_decide
