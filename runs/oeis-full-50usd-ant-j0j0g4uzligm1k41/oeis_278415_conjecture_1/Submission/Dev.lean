import FormalConjectures.Util.ProblemImports

open Nat

def A278415 (n : ℕ) : ℤ :=
  Finset.sum (Finset.range (n + 1)) fun k ↦
    (Nat.choose n (2 * k) : ℤ) * (Nat.choose (n - k) k : ℤ) * ((-1 : ℤ) ^ k)

open Padic

-- Reduction: the p-adic membership follows from an integer divisibility.
example (p : ℕ) [hp_prime : Fact p.Prime] (hp_gt_3 : p > 3) (n : ℕ) (hn_pos : 0 < n)
    (hkey : (p : ℤ) ^ (2 * (1 + padicValNat p n)) ∣ (A278415 (p * n) - A278415 n)) :
    ((Int.cast (A278415 (p * n)) - Int.cast (A278415 n)) / (Nat.cast (p * n) : Padic p) ^ 2)
      ∈ PadicInt.subring p := by
  rw [PadicInt.mem_subring_iff, ← Int.cast_sub, Padic.norm_le_one_iff_val_nonneg]
  set m : ℤ := A278415 (p * n) - A278415 n with hm
  have hpn : (p * n) ≠ 0 := by positivity
  have hpnQ : ((p * n : ℕ) : Padic p) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero.mpr hpn)
  have hpn2 : ((p * n : ℕ) : Padic p) ^ 2 ≠ 0 := pow_ne_zero _ hpnQ
  by_cases hz : m = 0
  · simp [hz]
  · have hmQ : (m : Padic p) ≠ 0 := by exact_mod_cast hz
    rw [div_eq_mul_inv, Padic.valuation_mul hmQ (inv_ne_zero hpn2), Padic.valuation_inv,
        Padic.valuation_pow, Padic.valuation_intCast, Padic.valuation_natCast]
    -- goal: 0 ≤ padicValInt p m - 2 * padicValNat p (p*n)
    have hval : padicValNat p (p * n) = 1 + padicValNat p n := by
      rw [padicValNat.mul (Nat.Prime.ne_zero hp_prime.out) (by omega), padicValNat_self]
    have hle : 2 * (1 + padicValNat p n) ≤ padicValInt p m := by
      have := (padicValInt_dvd_iff (2 * (1 + padicValNat p n)) m).mp hkey
      rcases this with h | h
      · exact absurd h hz
      · exact h
    rw [hval]
    omega
