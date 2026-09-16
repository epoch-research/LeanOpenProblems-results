import FormalConjectures.Util.ProblemImports

open Rat Nat

/--
A309132: $a(n)$ is the denominator of $F(n) = A027641(n-1)/n + A027642(n-1)/n^2$,
where $A027641(k)$ and $A027642(k)$ are the numerator and denominator of the $k$-th standard Bernoulli number $B_k$ ($B_1 = -1/2$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let n_q : ℚ := n
    have B_nm1 : ℚ := bernoulli (n - 1)
    let N : ℤ := B_nm1.num
    let D : ℕ := B_nm1.den

    -- F(n) = N / n + D / n^2, where division is rational division
    let q1 : ℚ := (N : ℚ) / n_q
    let q2 : ℚ := (D : ℚ) / (n_q * n_q)
    let F_n : ℚ := q1 + q2

    F_n.den

def a_comp (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let n_q : ℚ := n
    let B_nm1 : ℚ := bernoulli (n - 1)
    let N : ℤ := B_nm1.num
    let D : ℕ := B_nm1.den
    let q1 : ℚ := (N : ℚ) / n_q
    let q2 : ℚ := (D : ℚ) / (n_q * n_q)
    let F_n : ℚ := q1 + q2
    F_n.den

theorem a_eq_a_comp (n : ℕ) : a n = a_comp n := by
  by_cases h : n = 0
  · rw [a, a_comp, dif_pos h, if_pos h]
  · rw [a, a_comp, dif_neg h, if_neg h]

theorem oeis_309132_conjecture_key (n : ℕ) (hn : n > 1) : a n = 1 ↔ Nat.Prime n := by
  sorry

theorem oeis_309132_conjecture_key.disproof : ¬ (type_of% @oeis_309132_conjecture_key) := by
  intro h
  have h4 := h 4 (by norm_num)
  have ha4 : a 4 = 16 := by
    rw [a_eq_a_comp]
    native_decide
  have h_not_prime : ¬ Nat.Prime 4 := by norm_num
  rw [ha4] at h4
  have h16 : (16 = 1) ↔ False := by decide
  rw [h16] at h4
  -- At this point, h4 is False ↔ Nat.Prime 4.
  have hp : Nat.Prime 4 ↔ False := by
    constructor
    · intro h
      exact h_not_prime h
    · intro h
      exact False.elim h
  rw [hp] at h4
  -- h4 is False ↔ False
  -- From here I cannot get False.
  sorry
