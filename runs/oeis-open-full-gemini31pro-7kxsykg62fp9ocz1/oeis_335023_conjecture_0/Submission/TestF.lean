import FormalConjectures.Util.ProblemImports

open Nat Int Finset

def F_aux (n : ℕ) : ℤ :=
  if n < 2 then 0 else
  Finset.sum (Icc 2 n) $ fun k : ℕ =>
    let n_fact : ℤ := n.factorial
    let k_int : ℤ := k
    let quotient : ℤ := n_fact / k_int
    quotient * (if k % 2 = 0 then 1 else -1)

def P_def (a b : ℕ) : ℕ := ∏ k ∈ Ico a b, k

def term (a b k : ℕ) : ℤ :=
  (∏ j ∈ (Ico a b).erase k, (j : ℤ)) * (if k % 2 = 0 then 1 else -1)

def S_def (a b : ℕ) : ℤ :=
  ∑ k ∈ Ico a b, term a b k

lemma F_aux_eq_S_def (n : ℕ) (hn : 2 ≤ n) : F_aux n = S_def 2 (n + 1) := by
  dsimp [F_aux, S_def]
  rw [if_neg (by omega)]
  have h_ico : Ico 2 (n + 1) = Icc 2 n := Nat.Ico_succ_right
  rw [← h_ico]
  apply sum_congr rfl
  intro k hk
  dsimp [term]
  congr 1
  -- we need to prove `n! / k = \prod_{j \in Ico 2 (n+1) \setminus {k}} j`
  sorry

