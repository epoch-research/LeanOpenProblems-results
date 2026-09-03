import FormalConjecturesUtil

/-!
Exact elementary facts used in `LPFApproximationObstruction.md`.
This file does not import the specification or prove its density conjecture.
-/

namespace Erdos371Cutoff

/-- A multiplier below the threshold cannot change an absolute LPF cutoff. -/
theorem cutoff_mul_iff {n k y : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (hky : k ≤ y) :
    y < Nat.maxPrimeFac (k * n) ↔ y < Nat.maxPrimeFac n := by
  rw [Nat.maxPrimeFac_mul hk hn, lt_max_iff]
  have hpk : Nat.maxPrimeFac k ≤ y := Nat.maxPrimeFac_le.trans hky
  omega

/-- Below the square of the first allowed prime size, that prime is unique. -/
theorem large_prime_unique {n y p q : ℕ} (hn : 0 < n)
    (hsmall : n < (y + 1) * (y + 1))
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpd : p ∣ n) (hqd : q ∣ n) (hpy : y < p) (hqy : y < q) : p = q := by
  by_contra hne
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  have hle : p * q ≤ n := Nat.le_of_dvd hn (hcop.mul_dvd_of_dvd_of_dvd hpd hqd)
  have hlower : (y + 1) * (y + 1) ≤ p * q :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-- Exact cutoff averaging: no limiting statement or exceptional set is used. -/
theorem cutoff_sum {n H y : ℕ} (hn : n ≠ 0) (hH : H ≤ y) :
    (∑ k ∈ Finset.Icc 1 H,
      if y < Nat.maxPrimeFac (k * n) then (1 : ℝ) else 0) =
      (H : ℝ) * (if y < Nat.maxPrimeFac n then 1 else 0) := by
  calc
    _ = ∑ k ∈ Finset.Icc 1 H,
        (if y < Nat.maxPrimeFac n then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      obtain ⟨hk1, hkH⟩ := Finset.mem_Icc.mp hk
      simp only [cutoff_mul_iff hn (by omega) (hkH.trans hH)]
    _ = _ := by simp

#print axioms cutoff_mul_iff
#print axioms large_prime_unique
#print axioms cutoff_sum

end Erdos371Cutoff
