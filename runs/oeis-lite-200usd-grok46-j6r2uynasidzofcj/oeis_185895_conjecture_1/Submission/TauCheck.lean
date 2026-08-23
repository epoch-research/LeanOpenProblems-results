import FormalConjectures.Util.ProblemImports

open Nat

def tri' (m : ℕ) : ℕ := m * (m + 1) / 2

/-- DP row: `tauRow nMax k` has size `nMax+1` and stores `τ(d,k)` for `d ≤ nMax`. -/
def nextTauRow (nMax : ℕ) (k : ℕ) (prev : Array ℤ) : Array ℤ :=
  Array.ofFn (fun d : Fin (nMax + 1) =>
    if d.val < k + 1 then prev[d.val]!
    else prev[d.val]! - ((k + 1).factorial : ℤ) * prev[d.val - (k + 1)]!)

def tauRow (nMax : ℕ) : ℕ → Array ℤ
  | 0 => Array.ofFn (fun d : Fin (nMax + 1) => if d.val = 0 then (1 : ℤ) else 0)
  | k + 1 => nextTauRow nMax k (tauRow nMax k)

def nextWRow (nMax : ℕ) (k : ℕ) (prev : Array ℕ) : Array ℕ :=
  Array.ofFn (fun d : Fin (nMax + 1) =>
    if d.val < k + 1 then prev[d.val]!
    else prev[d.val]! + (k + 1).factorial * prev[d.val - (k + 1)]!)

def wRow (nMax : ℕ) : ℕ → Array ℕ
  | 0 => Array.ofFn (fun d : Fin (nMax + 1) => if d.val = 0 then 1 else 0)
  | k + 1 => nextWRow nMax k (wRow nMax k)

/-- Check `W(Δ+k+1,k) < |τ(Δ,k)| * (k+1)!` for `Δ ∈ {2k-3,2k-2,2k-1}`. -/
def checkCluster2 (k : ℕ) : Bool :=
  let nMax := 3 * k
  let τs := tauRow nMax k
  let Ws := wRow nMax k
  let fact := (k + 1).factorial
  let d0 := 2 * k - 3
  decide (
    Ws[d0 + k + 1]! < (τs[d0]!).natAbs * fact &&
    Ws[d0 + 1 + k + 1]! < (τs[d0 + 1]!).natAbs * fact &&
    Ws[d0 + 2 + k + 1]! < (τs[d0 + 2]!).natAbs * fact)

def checkCluster2_range (lo hi : ℕ) : Bool :=
  (List.range (hi + 1 - lo)).all fun i => checkCluster2 (lo + i)

def tri'' (m : ℕ) : ℕ := m * (m + 1) / 2
def midx'' (n : ℕ) : ℕ := Nat.findGreatest (fun m => tri'' m ≤ n) n

def checkAllPar (k : ℕ) : Bool :=
  let nMax := tri'' k + k + 1
  let τs := tauRow nMax k
  let Ws := wRow nMax k
  let fact := (k + 1).factorial
  (List.range (tri'' k + 1)).all fun n =>
    if k + 1 ≤ n then
      let rest := n - (k + 1)
      if decide (Even (midx'' n) ↔ Even (midx'' rest)) then
        let d := tri'' k - n
        if 2 * k - 3 ≤ d then
          decide (Ws[d + k + 1]! < (τs[d]!).natAbs * fact)
        else true
      else true
    else true

def checkAllParUpto (K : ℕ) : Bool :=
  Id.run do
    let nMax := tri'' K + K + 1
    let mut τ : Array ℤ :=
      Array.ofFn (fun d : Fin (nMax + 1) => if d.val = 0 then (1 : ℤ) else 0)
    let mut Wv : Array ℕ :=
      Array.ofFn (fun d : Fin (nMax + 1) => if d.val = 0 then 1 else 0)
    let mut ok := true
    for k in [0:K+1] do
      if 81 ≤ k then
        let fact := (k + 1).factorial
        for n in [k + 1:tri'' k + 1] do
          let rest := n - (k + 1)
          if decide (Even (midx'' n) ↔ Even (midx'' rest)) then
            let d := tri'' k - n
            if 2 * k - 3 ≤ d then
              if !(Wv[d + k + 1]! < (τ[d]!).natAbs * fact) then
                ok := false
      if k < K then
        τ := nextTauRow nMax k τ
        Wv := nextWRow nMax k Wv
    return ok

example : checkAllParUpto 120 = true := by native_decide
