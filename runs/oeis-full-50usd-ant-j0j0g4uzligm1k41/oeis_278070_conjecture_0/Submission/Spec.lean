import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A278070: $a(n) = \text{hypergeometric}([n, -n], [], -1)$.
This is equivalent to the combinatorial sum:
$$a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n+k-1}{k} k!$$
The expression uses $\mathbb{N}$ arithmetic throughout, safely handling the subtraction via `Nat.pred`.
-/
def A278070 (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k =>
    (n.choose k) * ((n + k).pred.choose k) * (k.factorial)

/-- The summand of `A278070` rewritten using the ascending factorial. -/
private def gg (N j : ℕ) : ℕ := N.choose j * N.ascFactorial j

private theorem gg_cast (N j : ℕ) :
    ((gg N j : ℤ)) = (N.choose j : ℤ) * (N.ascFactorial j : ℤ) := by
  simp [gg]

/-- Each summand of `A278070 N` equals `gg N j`. -/
private theorem term_eq (N j : ℕ) :
    N.choose j * (N + j).pred.choose j * j.factorial = gg N j := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose' N j
  rw [Nat.pred_eq_sub_one, gg, Nat.mul_assoc, h]
  ring

/-- `A278070 N` as a sum of `gg N j`. -/
private theorem A_eq (N : ℕ) :
    A278070 N = ∑ j ∈ Finset.range (N + 1), gg N j := by
  unfold A278070
  exact Finset.sum_congr rfl (fun j _ => term_eq N j)

/-- We can extend the range since the extra `choose` terms vanish. -/
private theorem A_eq' (N M : ℕ) (h : N + 1 ≤ M) :
    A278070 N = ∑ j ∈ Finset.range M, gg N j := by
  rw [A_eq N]
  apply Finset.sum_subset
  · intro x hx
    rw [Finset.mem_range] at hx ⊢; omega
  · intro j _ hj
    rw [Finset.mem_range] at hj
    simp only [gg]
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.zero_mul]

/-- Ascending-factorial congruence: shifting by `k` does not change it mod `k`. -/
private theorem ascF_modEq (n k : ℕ) :
    ∀ j, Nat.ModEq k ((n + k).ascFactorial j) (n.ascFactorial j) := by
  intro j
  induction j with
  | zero => simp [Nat.ascFactorial_zero, Nat.ModEq]
  | succ j ih =>
    rw [Nat.ascFactorial_succ, Nat.ascFactorial_succ]
    apply Nat.ModEq.mul _ ih
    have : n + k + j = (n + j) + k := by ring
    rw [this]
    exact Nat.add_modEq_right

/-- Integer version of the ascending-factorial congruence. -/
private theorem ascF_dvd (n k j : ℕ) :
    (k : ℤ) ∣ ((n + k).ascFactorial j : ℤ) - (n.ascFactorial j : ℤ) := by
  have h := (Nat.modEq_iff_dvd.mp (ascF_modEq n k j))
  have h2 := dvd_neg.mpr h
  rwa [neg_sub] at h2

/-- The key absorption divisibility: for `0 < i`, `k ∣ (k choose i) * ascFactorial n i`. -/
private theorem dvd_choose_ascF (n k i : ℕ) (hi : 0 < i) :
    k ∣ Nat.choose k i * Nat.ascFactorial n i := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [Nat.choose_eq_zero_of_lt hi, Nat.zero_mul]
  · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    -- `(i'+1) ∣ ascFactorial n (i'+1)`
    have hdvd : (i' + 1) ∣ Nat.ascFactorial n (i' + 1) :=
      dvd_trans (Nat.dvd_factorial (by omega) (le_refl _)) (Nat.factorial_dvd_ascFactorial n (i' + 1))
    obtain ⟨t, ht⟩ := hdvd
    have absorb : Nat.choose (k' + 1) (i' + 1) * (i' + 1) = (k' + 1) * Nat.choose k' i' :=
      (Nat.add_one_mul_choose_eq k' i').symm
    rw [ht]
    refine ⟨Nat.choose k' i' * t, ?_⟩
    calc
      Nat.choose (k' + 1) (i' + 1) * ((i' + 1) * t)
          = (Nat.choose (k' + 1) (i' + 1) * (i' + 1)) * t := by ring
      _ = ((k' + 1) * Nat.choose k' i') * t := by rw [absorb]
      _ = (k' + 1) * (Nat.choose k' i' * t) := by ring

/-- Vandermonde divisibility (integer version). -/
private theorem vand_dvd (n k j : ℕ) :
    (k : ℤ) ∣ ((n + k).choose j : ℤ) * (n.ascFactorial j : ℤ)
              - (n.choose j : ℤ) * (n.ascFactorial j : ℤ) := by
  -- the (0, j) entry of the antidiagonal
  have hmem : ((0 : ℕ), j) ∈ Finset.antidiagonal j := by
    simp [Finset.mem_antidiagonal]
  -- write the binomial sum as the (0,j) term + the rest
  have hsplit : ((n + k).choose j : ℤ)
      = (n.choose j : ℤ)
        + ∑ ij ∈ (Finset.antidiagonal j).erase (0, j),
            (k.choose ij.1 : ℤ) * (n.choose ij.2 : ℤ) := by
    rw [Nat.add_comm n k, Nat.add_choose_eq k n j]
    push_cast
    rw [← Finset.add_sum_erase _ _ hmem]
    simp
  rw [hsplit]
  have hcancel : ((n.choose j : ℤ)
        + ∑ ij ∈ (Finset.antidiagonal j).erase (0, j),
            (k.choose ij.1 : ℤ) * (n.choose ij.2 : ℤ)) * (n.ascFactorial j : ℤ)
        - (n.choose j : ℤ) * (n.ascFactorial j : ℤ)
      = (∑ ij ∈ (Finset.antidiagonal j).erase (0, j),
            (k.choose ij.1 : ℤ) * (n.choose ij.2 : ℤ)) * (n.ascFactorial j : ℤ) := by
    ring
  rw [hcancel, Finset.sum_mul]
  apply Finset.dvd_sum
  intro ij hij
  rw [Finset.mem_erase, Finset.mem_antidiagonal] at hij
  obtain ⟨hne, hsum⟩ := hij
  -- `ij.1 ≥ 1`
  have hi1 : 0 < ij.1 := by
    rcases Nat.eq_zero_or_pos ij.1 with h0 | h0
    · exfalso; apply hne
      have : ij.2 = j := by omega
      exact Prod.ext h0 this
    · exact h0
  -- split the ascending factorial
  have hAsc : n.ascFactorial j = n.ascFactorial ij.1 * (n + ij.1).ascFactorial ij.2 := by
    rw [Nat.ascFactorial_mul_ascFactorial]; rw [hsum]
  -- divisibility of the coefficient
  have hcoeff : (k : ℤ) ∣ (k.choose ij.1 : ℤ) * (n.ascFactorial ij.1 : ℤ) := by
    have := dvd_choose_ascF n k ij.1 hi1
    have := Int.natCast_dvd_natCast.mpr this
    rwa [Nat.cast_mul] at this
  -- assemble
  rw [hAsc]
  push_cast
  have hrw : (k.choose ij.1 : ℤ) * (n.choose ij.2 : ℤ)
        * ((n.ascFactorial ij.1 : ℤ) * ((n + ij.1).ascFactorial ij.2 : ℤ))
      = ((k.choose ij.1 : ℤ) * (n.ascFactorial ij.1 : ℤ))
        * ((n.choose ij.2 : ℤ) * ((n + ij.1).ascFactorial ij.2 : ℤ)) := by ring
  rw [hrw]
  exact Dvd.dvd.mul_right hcoeff _

/-- The key termwise divisibility. -/
private theorem key (n k j : ℕ) :
    (k : ℤ) ∣ (gg (n + k) j : ℤ) - (gg n j : ℤ) := by
  rw [gg_cast, gg_cast]
  have e : ((n + k).choose j : ℤ) * ((n + k).ascFactorial j : ℤ)
            - (n.choose j : ℤ) * (n.ascFactorial j : ℤ)
      = ((n + k).choose j : ℤ)
          * (((n + k).ascFactorial j : ℤ) - (n.ascFactorial j : ℤ))
        + (((n + k).choose j : ℤ) * (n.ascFactorial j : ℤ)
          - (n.choose j : ℤ) * (n.ascFactorial j : ℤ)) := by ring
  rw [e]
  exact dvd_add (Dvd.dvd.mul_left (ascF_dvd n k j) _) (vand_dvd n k j)

/--
We conjecture that a(n+k) == a(n) (mod k) for all n and k.
If true, then for each k, the sequence a(n) taken modulo k is a periodic sequence and the period divides k.
For example, modulo 7 the sequence becomes [1, 2, 4, 1, 1, 4, 2, 1, 2, 4, 1, 1, 4, 2, ...], apparently a periodic sequence of period 7.
-/
theorem oeis_278070_conjecture_0 : ∀ (n k : ℕ), Nat.ModEq k (A278070 (n + k)) (A278070 n) := by
  intro n k
  rw [Nat.modEq_iff_dvd]
  -- goal : (k : ℤ) ∣ ↑(A278070 n) - ↑(A278070 (n + k))
  have hA1 : A278070 (n + k) = ∑ j ∈ Finset.range (n + k + 1), gg (n + k) j := by
    rw [A_eq (n + k)]
  have hA2 : A278070 n = ∑ j ∈ Finset.range (n + k + 1), gg n j := by
    rw [A_eq' n (n + k + 1) (by omega)]
  rw [hA1, hA2]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro j _
  have h := dvd_neg.mpr (key n k j)
  rwa [neg_sub] at h
