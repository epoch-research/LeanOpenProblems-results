import FormalConjectures.Util.ProblemImports
open Finset Nat Set

def fastPrime (n : ℕ) : Bool := @decide (Nat.Prime n) (Nat.decidablePrime' n)
lemma fastPrime_eq (n : ℕ) : fastPrime n = true ↔ Nat.Prime n := by
  unfold fastPrime
  by_cases h : Nat.Prime n <;> simp [h]

def countBoolLoop (P : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n+1, acc => countBoolLoop P n (if P n then acc+1 else acc)
def countBool (P : ℕ → Bool) (n : ℕ) := countBoolLoop P n 0
lemma countBoolLoop_eq (P : ℕ → Bool) (Q : ℕ → Prop) [DecidablePred Q]
    (hPQ : ∀ n, P n = true ↔ Q n) (n acc : ℕ) :
    countBoolLoop P n acc = acc + Nat.count Q n := by
  induction n generalizing acc with
  | zero => simp [countBoolLoop]
  | succ n ih =>
      simp [countBoolLoop, ih]
      have := hPQ n
      by_cases hp : P n <;> by_cases hq : Q n <;> simp [hp, hq, Nat.count_succ, Nat.add_comm, Nat.add_left_comm] at *
lemma countBool_eq_count (P : ℕ → Bool) (Q : ℕ → Prop) [DecidablePred Q]
    (hPQ : ∀ n, P n = true ↔ Q n) (n : ℕ) : countBool P n = Nat.count Q n := by
  simp [countBool, countBoolLoop_eq P Q hPQ]

def primeCountFast (n : ℕ) : ℕ := countBool fastPrime n
lemma primeCountFast_eq (n) : primeCountFast n = Nat.primeCounting' n := by
  simp [primeCountFast, Nat.primeCounting', countBool_eq_count fastPrime Nat.Prime fastPrime_eq]

def lowerBound (B C p : ℕ) : ℕ :=
  ((Finset.Icc 2 B).filter Nat.Prime).sum
    (fun r => Nat.primeCounting' ((p + r - 1) / r) - Nat.primeCounting' (r + 1))
  + ((Finset.Icc 2 C).filter (fun q => Nat.Prime q ∧ q^3 < p)).card

def lowerBoundFast (B C p : ℕ) : ℕ :=
  ((Finset.Icc 2 B).filter (fun r => fastPrime r)).sum
    (fun r => primeCountFast ((p + r - 1) / r) - primeCountFast (r + 1))
  + ((Finset.Icc 2 C).filter (fun q => fastPrime q ∧ q^3 < p)).card
lemma lowerBoundFast_eq (B C p) : lowerBoundFast B C p = lowerBound B C p := by
  simp [lowerBoundFast, lowerBound, primeCountFast_eq, fastPrime_eq]

example : Nat.primeCounting' 20000000 = 1270607 := by
  rw [← primeCountFast_eq]
  native_decide
