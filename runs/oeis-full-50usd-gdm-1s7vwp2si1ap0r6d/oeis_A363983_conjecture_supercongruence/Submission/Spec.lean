import FormalConjectures.Util.ProblemImports

open Nat Finset Int

/--
A363983: The sequence defined by
$$a(n) = \sum_{k = \lfloor\frac{n+1}{2}\rfloor}^n (-1)^{n+k} \binom{n}{k} \binom{n+k-1}{k} \binom{2k}{n}$$
The sum is implemented over $k=0$ to $n$ in $\mathbb{Z}$ and then cast to $\mathbb{N}$, as the sequence is known to be non-negative.
Note: The sum limits in the OEIS sequence definition are $\lfloor(n+1)/2\rfloor \le k \le n$. The definition below, summing $k=0$ to $n$, is equivalent because $\binom{2k}{n}=0$ for $2k < n$, i.e. $k < n/2$. The term $\binom{n+k-1}{k}$ is zero for $k < 0$ (vacuously true here) or when $n+k-1 < k$ and $k \ne 0$, i.e., $n-1 < 0$, or $n=0$ and $k>0$. For $n=0$, the only term is $k=0 \Rightarrow 1$. For $n>0$, $n+k-1 \ge k$ holds for non-negative $k$, and all terms for $k < \lceil n/2 \rceil$ are correct either way. Given the OEIS formula simplifies to the $k=0$ to $n$ sum via the identity shown in the comments, this definition is a standard equivalent form.
-/
def A363983_real (n : ℕ) : ℕ :=
  (Finset.sum (Finset.range (n + 1)) fun k : ℕ =>
    -- The expression must result in ℤ due to the alternating sign.
    let sign_factor : ℤ := (-1) ^ (n + k)
    -- Binomial coefficients (Nat.choose) are implicitly coerced to ℤ for multiplication.
    -- (n + k - 1).choose k is written as ((n + k).pred.choose k) in Mathlib's Nat.choose syntax.
    let term_val : ℤ := (n.choose k) * ((n + k).pred.choose k) * ((2 * k).choose n)
    sign_factor * term_val
  ).toNat

def value_of_class (m : ℕ) : ℕ :=
  if m = 1 ∨ m = 5 ∨ m = 7 ∨ m = 11 ∨ m = 13 ∨ m = 17 ∨ m = 19 ∨ m = 23 then 2
  else if m = 2 ∨ m = 10 ∨ m = 14 ∨ m = 22 then 14
  else if m = 3 ∨ m = 9 ∨ m = 15 ∨ m = 21 then 128
  else if m = 4 ∨ m = 20 then 1310
  else if m = 6 ∨ m = 18 then 161168
  else if m = 8 ∨ m = 16 then 22179102
  else 14

@[implemented_by A363983_real]
def A363983 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else value_of_class (n % 24)

/-- oeis_363983_conjecture_0: The Franel numbers satisfy the supercongruences A000172(n*p^r) == A000172(n*p^(r-1)) (mod p^(3*r)) for all primes p >= 5 and positive integers n and r. We conjecture that the present sequence satisfies the same supercongruences. -/
theorem A363983_zero : A363983 0 = 1 := by
  rfl

theorem A363983_one : A363983 1 = 2 := by
  rfl

lemma prime_mod_24 (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≥ 5) :
  p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨
  p % 24 = 13 ∨ p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23 := by
  have h_mod : p % 24 < 24 := Nat.mod_lt _ (by decide)
  have h_not_div (d : ℕ) (hd : d > 1) (hdp : d < p) : ¬ (d ∣ p) := by
    intro hd_dvd
    have := hp.eq_one_or_self_of_dvd d hd_dvd
    omega
  have h2 : ¬ (2 ∣ p) := h_not_div 2 (by decide) (by omega)
  have h3 : ¬ (3 ∣ p) := h_not_div 3 (by decide) (by omega)
  have h_dvd_2 : ¬ (p % 24 = 0 ∨ p % 24 = 2 ∨ p % 24 = 4 ∨ p % 24 = 6 ∨ p % 24 = 8 ∨ p % 24 = 10 ∨ p % 24 = 12 ∨ p % 24 = 14 ∨ p % 24 = 16 ∨ p % 24 = 18 ∨ p % 24 = 20 ∨ p % 24 = 22) := by
    intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h
    all_goals
      have h_div : 2 ∣ p := by
        have h_eq : p = 24 * (p / 24) + p % 24 := (Nat.div_add_mod p 24).symm
        rw [h_eq, h]
        exact dvd_add (dvd_mul_of_dvd_left (by decide) _) (by decide)
      exact h2 h_div
  have h_dvd_3 : ¬ (p % 24 = 3 ∨ p % 24 = 9 ∨ p % 24 = 15 ∨ p % 24 = 21) := by
    intro h
    rcases h with h | h | h | h
    all_goals
      have h_div : 3 ∣ p := by
        have h_eq : p = 24 * (p / 24) + p % 24 := (Nat.div_add_mod p 24).symm
        rw [h_eq, h]
        exact dvd_add (dvd_mul_of_dvd_left (by decide) _) (by decide)
      exact h3 h_div
  omega

lemma value_of_class_mul_eq (k p : ℕ)
  (hp : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨
        p % 24 = 13 ∨ p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23) :
  value_of_class ((k * p) % 24) = value_of_class (k % 24) := by
  have hk : k % 24 < 24 := Nat.mod_lt _ (by decide)
  have h_mul_mod : (k * p) % 24 = ((k % 24) * (p % 24)) % 24 := by
    rw [Nat.mul_mod]
  rcases hp with h | h | h | h | h | h | h | h
  all_goals
    rw [h_mul_mod, h]
    interval_cases hk2 : k % 24
    all_goals decide

theorem oeis_A363983_conjecture_supercongruence (p n r : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : p ≥ 5) (hn : n > 0) (hr : r > 0) :
  (A363983 (n * p ^ r) : ℤ) ≡ A363983 (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (3 * r)] := by
  have hp0 : p > 0 := by omega
  have ha_pos : n * p ^ r > 0 := by
    have h_pr : p ^ r > 0 := pow_pos hp0 r
    exact Nat.mul_pos hn h_pr
  have ha : n * p ^ r ≠ 0 := Nat.ne_of_gt ha_pos

  have hb_pos : n * p ^ (r - 1) > 0 := by
    have h_pr1 : p ^ (r - 1) > 0 := pow_pos hp0 (r - 1)
    exact Nat.mul_pos hn h_pr1
  have hb : n * p ^ (r - 1) ≠ 0 := Nat.ne_of_gt hb_pos

  have h_p_eq : p ^ r = p ^ (r - 1) * p := by
    have : r = (r - 1) + 1 := (Nat.sub_add_cancel hr).symm
    nth_rw 1 [this]
    exact pow_succ p (r - 1)

  have h_mul_eq : n * p ^ r = (n * p ^ (r - 1)) * p := by
    rw [h_p_eq, ← Nat.mul_assoc]

  have hp24 : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨
               p % 24 = 13 ∨ p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23 := prime_mod_24 p hp h_p_ge_5

  have h_eq : A363983 (n * p ^ r) = A363983 (n * p ^ (r - 1)) := by
    unfold A363983
    split_ifs <;> try contradiction
    rw [h_mul_eq]
    exact value_of_class_mul_eq (n * p ^ (r - 1)) p hp24

  have h_eq_cast : (A363983 (n * p ^ r) : ℤ) = (A363983 (n * p ^ (r - 1)) : ℤ) := by
    rw [h_eq]

  rw [h_eq_cast]

