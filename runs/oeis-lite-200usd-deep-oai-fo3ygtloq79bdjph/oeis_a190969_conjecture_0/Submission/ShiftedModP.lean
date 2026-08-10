import FormalConjectures.Util.ProblemImports

open Finset Nat Polynomial
open scoped BigOperators

/-- A small nonzero natural below a prime remains nonzero in `ZMod p`. -/
lemma zmod_nat_cast_ne_zero_of_lt_prime {p m : ℕ} (_hp : p.Prime) (hm0 : 0 < m) (hmp : m < p) :
    (m : ZMod p) ≠ 0 := by
  intro h
  have hdiv : p ∣ m := by simpa [ZMod.natCast_eq_zero_iff] using h
  have hp_le : p ≤ m := Nat.le_of_dvd hm0 hdiv
  omega

/-- The linear relation used in the standard proof that shifted-Legendre coefficients reduce to
Hasse-binomial coefficients modulo `p` when `p=2n+1`: in `ZMod p`, `n+k+1 = -(n-k)`. -/
lemma zmod_half_index_sum_neg {p n k : ℕ} (hp_eq : p = 2 * n + 1) (hk : k ≤ n) :
    ((n + k + 1 : ℕ) : ZMod p) = - ((n - k : ℕ) : ZMod p) := by
  have hpzero : ((p : ℕ) : ZMod p) = 0 := by simp
  have hnat : n + k + 1 + (n - k) = p := by omega
  have h := congrArg (fun x : ℕ => (x : ZMod p)) hnat
  simp only [Nat.cast_add, Nat.cast_one] at h
  rw [hpzero] at h
  linear_combination h

/-- Multiplicative form of the Pascal-ratio identity for `n.choose (k+1)`, cast to `ZMod p`.
This avoids needing a field/division instance in the statement. -/
lemma choose_succ_right_zmod_mul {p n k : ℕ} :
    ((n.choose (k + 1) : ℕ) : ZMod p) * (k + 1 : ZMod p) =
      (n.choose k : ZMod p) * (n - k : ZMod p) := by
  have h := congrArg (fun x : ℕ => (x : ZMod p)) (Nat.choose_succ_right_eq n k)
  simpa only [Nat.cast_mul] using h

/-- Multiplicative form of the ratio identity for `(n+k+1).choose (k+1)`, cast to `ZMod p`. -/
lemma choose_add_succ_zmod_mul {p n k : ℕ} :
    (((n + k + 1).choose (k + 1) : ℕ) : ZMod p) * (k + 1 : ZMod p) =
      ((n + k).choose k : ZMod p) * (n + k + 1 : ZMod p) := by
  have h := congrArg (fun x : ℕ => (x : ZMod p)) (Nat.add_one_mul_choose_eq (n + k) k)
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h.symm
