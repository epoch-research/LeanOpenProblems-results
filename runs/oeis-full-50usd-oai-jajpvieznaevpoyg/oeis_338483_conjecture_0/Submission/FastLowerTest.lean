import FormalConjectures.Util.ProblemImports
open Finset Nat Set

def countPredLoop (P : ℕ → Prop) [DecidablePred P] : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n+1, acc => countPredLoop P n (if P n then acc+1 else acc)
def countPredFast (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : ℕ := countPredLoop P n 0
lemma countPredLoop_eq (P : ℕ → Prop) [DecidablePred P] (n acc : ℕ) :
    countPredLoop P n acc = acc + Nat.count P n := by
  induction n generalizing acc with
  | zero => simp [countPredLoop]
  | succ n ih => simp [countPredLoop, ih, Nat.count_succ]; by_cases h:P n <;> simp [h, Nat.add_comm, Nat.add_left_comm]
lemma countPredFast_eq (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : countPredFast P n = Nat.count P n := by simp [countPredFast, countPredLoop_eq]
def primeCountFast (n : ℕ) : ℕ := countPredFast Nat.Prime n
lemma primeCountFast_eq (n) : primeCountFast n = Nat.primeCounting' n := by simp [primeCountFast, Nat.primeCounting', countPredFast_eq]

def lowerBound (B C p : ℕ) : ℕ :=
  ((Finset.Icc 2 B).filter Nat.Prime).sum
    (fun r => Nat.primeCounting' ((p + r - 1) / r) - Nat.primeCounting' (r + 1))
  + ((Finset.Icc 2 C).filter (fun q => Nat.Prime q ∧ q^3 < p)).card

def lowerBoundFast (B C p : ℕ) : ℕ :=
  ((Finset.Icc 2 B).filter Nat.Prime).sum
    (fun r => primeCountFast ((p + r - 1) / r) - primeCountFast (r + 1))
  + ((Finset.Icc 2 C).filter (fun q => Nat.Prime q ∧ q^3 < p)).card

lemma lowerBoundFast_eq (B C p) : lowerBoundFast B C p = lowerBound B C p := by
  simp [lowerBoundFast, lowerBound, primeCountFast_eq]

example : lowerBound 1013 1000 39449933 = 6374065 := by
  rw [← lowerBoundFast_eq]
  native_decide
example : Nat.primeCounting' 100000000 = 5761455 := by
  rw [← primeCountFast_eq]
  native_decide
