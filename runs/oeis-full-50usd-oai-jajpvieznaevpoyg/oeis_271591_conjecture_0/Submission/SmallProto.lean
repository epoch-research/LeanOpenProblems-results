import FormalConjectures.Util.ProblemImports
open Nat

def tribonacci (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => (tribonacci (n + 2)) + (tribonacci (n + 1)) + (tribonacci n)
def a (n : ℕ) : ℕ :=
  let T := tribonacci n
  if h : T ≤ 1 then 0 else
    let j_smsb : ℕ := T.log2 - 1
    if T.testBit j_smsb then 1 else 0
def is_maximal_run (v : ℕ) (n L : ℕ) : Prop :=
  n ≥ 2 ∧ L ≥ 1 ∧ (∀ i : ℕ, i < L → a (n + i) = v) ∧ (a (n + L) ≠ v) ∧ (a (n - 1) ≠ v)

lemma small0 {n L} (hn:n<10) (h:is_maximal_run 0 n L): L=4∨L=5 := by
  interval_cases n <;> unfold is_maximal_run at h <;> norm_num [a, tribonacci] at h ⊢
  all_goals try omega
