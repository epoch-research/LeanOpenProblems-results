import FormalConjectures.Util.ProblemImports

open Finset Nat

lemma centralBinom_le_pow_primeCounting (m : ℕ) (hm : 0 < m) :
    Nat.centralBinom m ≤ (2 * m) ^ Nat.primeCounting' (2 * m + 1) := by
  rw [← Nat.prod_pow_factorization_centralBinom m]
  let S := {p ∈ Finset.range (2 * m + 1) | Nat.Prime p}
  have hprod : (∏ p ∈ Finset.range (2 * m + 1), p ^ (Nat.centralBinom m).factorization p)
      = ∏ p ∈ S, p ^ (Nat.centralBinom m).factorization p := by
    symm
    refine Finset.prod_subset (by intro x hx; exact (Finset.mem_filter.mp hx).1) ?_
    intro x hx hxS
    have hnot : ¬ Nat.Prime x := by
      intro hp
      exact hxS (Finset.mem_filter.mpr ⟨hx, hp⟩)
    rw [Nat.factorization_eq_zero_of_not_prime _ hnot, pow_zero]
  rw [hprod]
  calc
    (∏ p ∈ S, p ^ (Nat.centralBinom m).factorization p) ≤ ∏ p ∈ S, (2 * m) := by
      refine Finset.prod_le_prod' ?_
      intro p hp
      exact Nat.pow_factorization_choose_le (n := 2*m) (k := m) (p := p) (by positivity)
    _ = (2 * m) ^ S.card := by simp
    _ ≤ (2 * m) ^ Nat.primeCounting' (2 * m + 1) := by
      apply Nat.pow_le_pow_right
      · positivity
      · dsimp [S]
        rw [← Nat.primesBelow_card_eq_primeCounting']
        rfl

lemma primeCounting'_gt_of_mul_pow_lt_four_pow {m r : ℕ} (hm : 4 ≤ m)
    (hineq : m * (2 * m) ^ r < 4 ^ m) :
    r < Nat.primeCounting' (2 * m + 1) := by
  by_contra hnot
  have hle : Nat.primeCounting' (2 * m + 1) ≤ r := Nat.le_of_not_gt hnot
  have hcb := centralBinom_le_pow_primeCounting m (by omega : 0 < m)
  have hpow : (2 * m) ^ Nat.primeCounting' (2 * m + 1) ≤ (2 * m) ^ r := by
    exact Nat.pow_le_pow_right (by omega : 0 < 2 * m) hle
  have hupper : m * Nat.centralBinom m ≤ m * (2 * m) ^ r := by
    exact Nat.mul_le_mul_left m (le_trans hcb hpow)
  have hlower : 4 ^ m < m * Nat.centralBinom m := Nat.four_pow_lt_mul_centralBinom m hm
  exact (lt_of_lt_of_le hlower hupper).not_ge hineq.le

lemma nth_prime_lt_of_primeCounting'_gt {i N : ℕ}
    (hcnt : i < Nat.primeCounting' N) : Nat.nth Nat.Prime i < N := by
  by_contra hnot
  have hleN : N ≤ Nat.nth Nat.Prime i := Nat.le_of_not_gt hnot
  have hmono := Nat.monotone_primeCounting' hleN
  rw [Nat.primeCounting'_nth_eq] at hmono
  exact (not_lt_of_ge hmono) hcnt

lemma nth_prime_le_two_mul_of_mul_pow_lt_four_pow {m r : ℕ} (hm : 4 ≤ m)
    (hineq : m * (2 * m) ^ r < 4 ^ m) :
    Nat.nth Nat.Prime r < 2 * m + 1 := by
  exact nth_prime_lt_of_primeCounting'_gt (primeCounting'_gt_of_mul_pow_lt_four_pow hm hineq)
