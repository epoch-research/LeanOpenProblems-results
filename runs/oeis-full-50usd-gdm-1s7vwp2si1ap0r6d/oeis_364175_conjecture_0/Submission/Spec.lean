import FormalConjectures.Util.ProblemImports

open Real Nat Int

@[category API, AMS 11]
lemma prime_dvd_pow_iff {p m : ℕ} {n : ℕ} (hp : p.Prime) (hn : n ≠ 0) : p ∣ m ^ n ↔ p ∣ m := by
  constructor
  · apply hp.dvd_of_dvd_pow
  · intro h
    have : m ∣ m ^ n := dvd_pow_self m hn
    exact dvd_trans h this

@[category API, AMS 11]
lemma dvd_iff_dvd_of_prime_ge_five {d n p r : ℕ} (hd : d.Prime) (hd_lt : d < p) (hp : p.Prime) (hr : r ≠ 0) :
  (d ∣ n * p ^ r) ↔ (d ∣ n) := by
  rw [Nat.Prime.dvd_mul hd, prime_dvd_pow_iff hd hr]
  have h_not_dvd : ¬ (d ∣ p) := by
    intro hd_dvd
    have h_le := Nat.le_of_dvd hp.pos hd_dvd
    have h_eq_or_one : d = 1 ∨ d = p := (Nat.Prime.eq_one_or_self_of_dvd hp d hd_dvd)
    rcases h_eq_or_one with h1 | hp_eq
    · subst h1
      exact Nat.Prime.ne_one hd rfl
    · subst hp_eq
      omega
  simp [h_not_dvd]



/--
A364175: $a(n) = \frac{(6n)! (2n/3)!}{(3n)! (2n)! (5n/3)!}$.
The fractional factorial $x!$ is defined as $\Gamma(x+1)$.
This sequence is only conjecturally an integer sequence. We round the real-valued result to obtain a natural number.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat

theorem oeis_364175_conjecture_0 (p n r : ℕ) (hp : p.Prime) (h_prime_ge_five : 5 ≤ p)
  (hn : 0 < n) (hr : 0 < r) :
  a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  sorry


