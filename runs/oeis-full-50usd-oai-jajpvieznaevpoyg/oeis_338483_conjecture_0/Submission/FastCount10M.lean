import FormalConjectures.Util.ProblemImports

def fastPrime (n : ℕ) : Bool := @decide (Nat.Prime n) (Nat.decidablePrime' n)
lemma fastPrime_eq (n : ℕ) : fastPrime n = true ↔ Nat.Prime n := by
  unfold fastPrime; by_cases h : Nat.Prime n <;> simp [h]
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
example : Nat.count Nat.Prime 10000019 = 664579 := by
  rw [← countBool_eq_count fastPrime Nat.Prime fastPrime_eq]
  native_decide
