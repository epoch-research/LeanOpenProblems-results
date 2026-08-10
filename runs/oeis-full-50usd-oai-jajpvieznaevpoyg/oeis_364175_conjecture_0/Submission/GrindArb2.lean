import FormalConjectures.Util.ProblemImports

lemma r_ne_p_pow_pred {p r : ℕ} (hp : 5 ≤ p) (hr : 0 < r) : r ≠ p ^ (r - 1) := by
  intro h
  cases r with
  | zero => cases hr
  | succ k =>
    cases k with
    | zero => norm_num at h hp
    | succ k =>
      have hp2 : 2 ≤ p := by omega
      have hpow : (k+2 : ℕ) < p ^ (k+1) := by
        calc
          k + 2 < 2 ^ (k+1) := by
            exact Nat.lt_two_pow_self (k+2) -- likely wrong
          _ ≤ p ^ (k+1) := by gcongr
      omega

example (f : ℕ → ℕ) (p n r : ℕ) (hp : p.Prime) (h_prime_ge_five : 5 ≤ p)
  (hn : 0 < n) (hr : 0 < r) :
  f (n * p ^ r) ≡ f (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have hnp := r_ne_p_pow_pred (p:=p) (r:=r) h_prime_ge_five hr
  grind [Nat.ModEq]
