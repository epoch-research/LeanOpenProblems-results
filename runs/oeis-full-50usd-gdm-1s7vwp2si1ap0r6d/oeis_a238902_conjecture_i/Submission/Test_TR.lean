import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime
set_option maxRecDepth 100000

def count_tr (p : ℕ → Prop) [DecidablePred p] : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n + 1, acc => count_tr p n (acc + if p n then 1 else 0)

theorem count_tr_eq (p : ℕ → Prop) [DecidablePred p] (n : ℕ) (acc : ℕ) :
    count_tr p n acc = acc + Nat.count p n := by
  induction n generalizing acc with
  | zero => simp [count_tr, Nat.count_zero]
  | succ n ih =>
    rw [count_tr]
    rw [ih]
    rw [Nat.count_succ]
    omega

def π_tr (n : ℕ) : ℕ := count_tr Nat.Prime (n + 1) 0

theorem π_tr_eq (n : ℕ) : π_tr n = π n := by
  unfold π_tr
  change count_tr Nat.Prime (n + 1) 0 = Nat.count Nat.Prime (n + 1)
  rw [count_tr_eq]
  simp

set_option maxHeartbeats 5000000

theorem test_1440 : π_tr (π_tr 1440) = 49 := by rfl
