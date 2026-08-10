import FormalConjectures.Util.ProblemImports

open Nat

/--
A278415: The sum $\sum_{k=0}^n \binom{n}{2k} \binom{n-k}{k}(-1)^k$.
-/
def A278415 (n : ℕ) : ℤ :=
  Finset.sum (Finset.range (n + 1)) fun k ↦
    (Nat.choose n (2 * k) : ℤ) * (Nat.choose (n - k) k : ℤ) * ((-1 : ℤ) ^ k)

open Padic

/-- The integer form of the supercongruence: `p ^ (2 * v_p(p*n))` divides
`A278415 (p*n) - A278415 n`, where `v_p(p*n) = 1 + v_p(n)`. -/
theorem A278415_supercongruence
    (p : ℕ) [hp_prime : Fact p.Prime] (hp_gt_3 : p > 3) (n : ℕ) (hn_pos : 0 < n) :
    (p : ℤ) ^ (2 * (1 + padicValNat p n)) ∣ (A278415 (p * n) - A278415 n) := by
  sorry

/--
oeis_278415_conjecture_1: Conjecture: For any prime $p > 3$ and positive integer $n$, the number $(A278415(p \cdot n) - A278415(n))/(p \cdot n)^2$ is always a $p$-adic integer.
-/
theorem oeis_278415_conjecture_1 (p : ℕ) [hp_prime : Fact p.Prime] (hp_gt_3 : p > 3) (n : ℕ) (hn_pos : 0 < n) :
    (by exact ((Int.cast (A278415 (p * n)) - Int.cast (A278415 n)) / (Nat.cast (p * n) : Padic p) ^ 2) ∈ PadicInt.subring p) :=
  by
  rw [PadicInt.mem_subring_iff, ← Int.cast_sub, Padic.norm_le_one_iff_val_nonneg]
  set m : ℤ := A278415 (p * n) - A278415 n with hm
  have hkey : (p : ℤ) ^ (2 * (1 + padicValNat p n)) ∣ m :=
    A278415_supercongruence p hp_gt_3 n hn_pos
  have hpn : (p * n) ≠ 0 := by positivity
  have hpnQ : ((p * n : ℕ) : Padic p) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero.mpr hpn)
  have hpn2 : ((p * n : ℕ) : Padic p) ^ 2 ≠ 0 := pow_ne_zero _ hpnQ
  by_cases hz : m = 0
  · simp [hz]
  · have hmQ : (m : Padic p) ≠ 0 := by exact_mod_cast hz
    rw [div_eq_mul_inv, Padic.valuation_mul hmQ (inv_ne_zero hpn2), Padic.valuation_inv,
        Padic.valuation_pow, Padic.valuation_intCast, Padic.valuation_natCast]
    have hval : padicValNat p (p * n) = 1 + padicValNat p n := by
      rw [padicValNat.mul (Nat.Prime.ne_zero hp_prime.out) (by omega), padicValNat_self]
    have hle : 2 * (1 + padicValNat p n) ≤ padicValInt p m := by
      have := (padicValInt_dvd_iff (2 * (1 + padicValNat p n)) m).mp hkey
      rcases this with h | h
      · exact absurd h hz
      · exact h
    rw [hval]
    omega
