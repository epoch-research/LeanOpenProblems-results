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
  | succ n ih =>
      simp [countPredLoop, ih, Nat.count_succ]
      by_cases h : P n <;> simp [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma countPredFast_eq (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    countPredFast P n = Nat.count P n := by
  simp [countPredFast, countPredLoop_eq]

example : Nat.primeCounting' 10000000 = 664579 := by
  unfold Nat.primeCounting'
  rw [← countPredFast_eq Nat.Prime]
  native_decide
