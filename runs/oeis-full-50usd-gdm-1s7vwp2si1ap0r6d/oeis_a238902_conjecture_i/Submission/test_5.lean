import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

set_option maxHeartbeats 20000000
set_option maxRecDepth 10000

theorem count_add (p : ℕ → Prop) [DecidablePred p] (n m : ℕ) :
    Nat.count p (n + m) = Nat.count p n + Nat.count (fun x => p (x + n)) m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h_comm : m + n = n + m := Nat.add_comm m n
    rw [Nat.add_succ, Nat.count_succ, ih, Nat.count_succ]
    rw [h_comm]
    omega

theorem pi_200 : Nat.count Nat.Prime 200 = 46 := by decide

theorem pi_400 : Nat.count Nat.Prime 400 = 78 := by
  have h : 400 = 200 + 200 := by omega
  rw [h, count_add, pi_200]
  decide

theorem pi_600 : Nat.count Nat.Prime 600 = 109 := by
  have h : 600 = 400 + 200 := by omega
  rw [h, count_add, pi_400]
  decide

theorem pi_800 : Nat.count Nat.Prime 800 = 139 := by
  have h : 800 = 600 + 200 := by omega
  rw [h, count_add, pi_600]
  decide

theorem pi_896 : π 896 = 154 := by
  change Nat.count Nat.Prime 897 = 154
  have h : 897 = 800 + 97 := by omega
  rw [h, count_add, pi_800]
  decide

theorem pi_910 : π 910 = 155 := by
  change Nat.count Nat.Prime 911 = 155
  have h : 911 = 800 + 111 := by omega
  rw [h, count_add, pi_800]
  decide

theorem pi_1000 : Nat.count Nat.Prime 1000 = 168 := by
  have h : 1000 = 800 + 200 := by omega
  rw [h, count_add, pi_800]
  decide

theorem pi_1200 : Nat.count Nat.Prime 1200 = 196 := by
  have h : 1200 = 1000 + 200 := by omega
  rw [h, count_add, pi_1000]
  decide

theorem pi_1400 : Nat.count Nat.Prime 1400 = 222 := by
  have h : 1400 = 1200 + 200 := by omega
  rw [h, count_add, pi_1200]
  decide

theorem pi_1440 : π 1440 = 227 := by
  change Nat.count Nat.Prime 1441 = 227
  have h : 1441 = 1400 + 41 := by omega
  rw [h, count_add, pi_1400]
  decide





