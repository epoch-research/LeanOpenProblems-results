import FormalConjectures.Util.ProblemImports

open Nat

/--
A275027: $a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n-k}{k}$.
-/
def A275027 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) (fun k => (Nat.choose n k) ^ 2 * (Nat.choose (n - k) k))

open Padic

/-- The arithmetic core of the conjecture: the integer `a(p*n) - a(n)` is divisible by
`p ^ (3 * (1 + v_p(n)))`, equivalently `(p*n)^3` divides it `p`-adically. -/
theorem A275027_core {p : ℕ} (hp : Nat.Prime p) (hp5 : p > 5) {n : ℕ} (hn : n > 0) :
    (p : ℤ) ^ (3 * (1 + n.factorization p)) ∣ ((A275027 (p * n) : ℤ) - (A275027 n : ℤ)) := by
  sorry

/-- A275027 Conjecture: For any prime p > 5 and positive integer n,
the number (a(p*n)-a(n))/(p*n)^3 is always a p-adic integer. -/
theorem oeis_275027_conjecture_0
    {p : ℕ} (hp : Nat.Prime p) (hp_gt_5 : p > 5)
    {n : ℕ} (hn_pos : n > 0) :
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    let num : ℚ := (A275027 (p * n) : ℚ) - (A275027 n : ℚ)
    let den : ℚ := (p * n : ℚ) ^ 3
    let val_Q : ℚ := num / den
    (val_Q : Padic p) ∈ PadicInt.subring p := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  intro num den val_Q
  rw [PadicInt.mem_subring_iff, Padic.eq_padicNorm]
  by_cases hz : val_Q = 0
  · simp [hz]
  · rw [padicNorm, if_neg hz]
    rw [show (1 : ℝ) = ((1 : ℚ) : ℝ) by norm_num, Rat.cast_le]
    apply zpow_le_one_of_nonpos₀ (by exact_mod_cast hp.one_le)
    rw [neg_nonpos]
    have hnum0 : num ≠ 0 := by
      intro h; apply hz; simp [val_Q, h]
    have hden0 : den ≠ 0 := by
      have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn_pos.ne'
      simp only [den]; positivity
    set D : ℤ := (A275027 (p * n) : ℤ) - (A275027 n : ℤ) with hD
    have hnumD : num = (D : ℚ) := by push_cast [hD, num]; ring
    have hD0 : D ≠ 0 := by
      intro h; apply hnum0; rw [hnumD, h]; simp
    have hval : padicValRat p val_Q = padicValRat p num - padicValRat p den := by
      simp only [val_Q]; exact padicValRat.div hnum0 hden0
    rw [hval, sub_nonneg]
    have hnumval : padicValRat p num = (padicValInt p D : ℤ) := by
      rw [hnumD, padicValRat.of_int]
    have hdeneq : den = (((p * n : ℕ) : ℚ)) ^ 3 := by push_cast [den]; ring
    have hpn0 : ((p * n : ℕ) : ℚ) ≠ 0 := by
      have : p * n ≠ 0 := Nat.mul_ne_zero hp.ne_zero hn_pos.ne'
      exact_mod_cast this
    have hdenval : padicValRat p den = 3 * (padicValNat p (p * n) : ℤ) := by
      rw [hdeneq, padicValRat.pow hpn0, padicValRat_of_nat]; ring
    rw [hnumval, hdenval]
    have hfac : padicValNat p (p * n) = 1 + n.factorization p := by
      rw [padicValNat.mul hp.ne_zero hn_pos.ne', padicValNat.self hp.one_lt]
      congr 1
      rw [Nat.factorization_def _ hp]
    rw [hfac]
    have hcore : (p : ℤ) ^ (3 * (1 + n.factorization p)) ∣ D := A275027_core hp hp_gt_5 hn_pos
    rw [padicValInt_dvd_iff] at hcore
    rcases hcore with h | h
    · exact absurd h hD0
    · exact_mod_cast h
