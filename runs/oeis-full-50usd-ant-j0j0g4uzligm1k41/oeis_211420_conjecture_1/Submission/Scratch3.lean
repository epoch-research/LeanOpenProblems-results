import Mathlib
open Finset Nat
set_option maxHeartbeats 1000000

axiom keyfloor_nat (q n r : ℕ) (hq : 0 < q) (hr : r ≤ 4*n) :
    2*n/q + 3*n/q + (4*n-r)/q ≤ 8*r/q + n/q + (8*n-2*r)/q

theorem TARGET (n r : ℕ) (hr : r ≤ 4*n) :
    (2*n)! * (3*n)! * (4*n-r)! ∣ (8*r)! * n ! * (8*n-2*r)! := by
  have hf : ∀ m : ℕ, (m ! : ℕ) ≠ 0 := fun m => Nat.factorial_ne_zero m
  rw [← Nat.factorization_le_iff_dvd
      (mul_ne_zero (mul_ne_zero (hf _) (hf _)) (hf _))
      (mul_ne_zero (mul_ne_zero (hf _) (hf _)) (hf _)), Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · set b := 8*n + 8*r + 1 with hb
    have hlt : ∀ k : ℕ, k ≤ 8*n+8*r → Nat.log p k < b := fun k hk =>
      lt_of_le_of_lt (Nat.log_le_self p k) (by omega)
    have f1 : ((2*n)!).factorization p = ∑ i ∈ Ico 1 b, 2*n/p^i :=
      Nat.factorization_factorial hp (hlt (2*n) (by omega))
    have f2 : ((3*n)!).factorization p = ∑ i ∈ Ico 1 b, 3*n/p^i :=
      Nat.factorization_factorial hp (hlt (3*n) (by omega))
    have f3 : ((4*n-r)!).factorization p = ∑ i ∈ Ico 1 b, (4*n-r)/p^i :=
      Nat.factorization_factorial hp (hlt (4*n-r) (by omega))
    have f4 : ((8*r)!).factorization p = ∑ i ∈ Ico 1 b, 8*r/p^i :=
      Nat.factorization_factorial hp (hlt (8*r) (by omega))
    have f5 : ((n)!).factorization p = ∑ i ∈ Ico 1 b, n/p^i :=
      Nat.factorization_factorial hp (hlt n (by omega))
    have f6 : ((8*n-2*r)!).factorization p = ∑ i ∈ Ico 1 b, (8*n-2*r)/p^i :=
      Nat.factorization_factorial hp (hlt (8*n-2*r) (by omega))
    rw [Nat.factorization_mul (mul_ne_zero (hf _) (hf _)) (hf _),
        Nat.factorization_mul (hf _) (hf _),
        Nat.factorization_mul (mul_ne_zero (hf _) (hf _)) (hf _),
        Nat.factorization_mul (hf _) (hf _)]
    simp only [Finsupp.coe_add, Pi.add_apply, f1, f2, f3, f4, f5, f6]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    exact keyfloor_nat (p^i) n r (pow_pos hp.pos i) hr
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
