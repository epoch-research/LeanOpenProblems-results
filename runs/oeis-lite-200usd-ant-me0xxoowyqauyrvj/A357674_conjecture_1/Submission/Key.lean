import FormalConjectures.Util.ProblemImports
open Nat Finset BigOperators

namespace Key

variable {p : ℕ}

/-- Power sum over `Ico 1 p` in `ZMod (p^3)`. -/
noncomputable def S (p m : ℕ) : ZMod (p^3) := ∑ k ∈ Ico 1 p, (k : ZMod (p^3))^m

/-- Harmonic sum of inverse squares in `ZMod (p^3)`. -/
noncomputable def H2 (p : ℕ) : ZMod (p^3) := ∑ k ∈ Ico 1 p, ((k : ZMod (p^3)))⁻¹^2

theorem pcube_zero [Fact p.Prime] : (p:ZMod (p^3))^3 = 0 := by
  have h := ZMod.natCast_self (p^3); push_cast at h; exact h

/-- Per-term inverse-power identity in `ZMod (p^3)`:
`k⁻² = 3 k^{p-3} - 3 k^{2p-4} + k^{3p-5}`. -/
theorem inv_sq_term [Fact p.Prime] (hp : 5 ≤ p) (k : ZMod (p^3)) (hk : IsUnit k)
    (hu : (p : ZMod (p^3)) ∣ (k^(p-1) - 1)) :
    k⁻¹^2 = 3 * k^(p-3) - 3 * k^(2*p-4) + k^(3*p-5) := by
  have hp3 : (p:ZMod (p^3))^3 = 0 := pcube_zero
  obtain ⟨t, ht⟩ := hu
  have hzero : (k^(p-1) - 1)^3 = 0 := by rw [ht, mul_pow, hp3]; ring
  have hpoly : 3*k^(p-1) - 3*(k^(p-1))^2 + (k^(p-1))^3 = 1 := by
    linear_combination hzero
  have conv : ∀ m : ℕ, 1 ≤ m → k^(m*(p-1) - 2) * k^2 = (k^(p-1))^m := by
    intro m hm
    rw [← pow_add, ← pow_mul]
    congr 1
    have h2 : 2 ≤ m*(p-1) := by
      have : 1 * 4 ≤ m * (p-1) := Nat.mul_le_mul hm (by omega)
      omega
    rw [Nat.sub_add_cancel h2, Nat.mul_comm]
  have hkk : k⁻¹^2 * k^2 = 1 := by
    have h1 : k⁻¹ * k = 1 := ZMod.inv_mul_of_unit k hk
    calc k⁻¹^2 * k^2 = (k⁻¹*k)^2 := by ring
      _ = 1 := by rw [h1]; ring
  have hR : (3 * k^(p-3) - 3 * k^(2*p-4) + k^(3*p-5)) * k^2 = 1 := by
    have c1 := conv 1 (by omega); have c2 := conv 2 (by omega); have c3 := conv 3 (by omega)
    have e1 : p - 3 = 1*(p-1)-2 := by omega
    have e2 : 2*p - 4 = 2*(p-1)-2 := by omega
    have e3 : 3*p - 5 = 3*(p-1)-2 := by omega
    rw [e1, e2, e3]
    have expand : (3 * k^(1*(p-1)-2) - 3 * k^(2*(p-1)-2) + k^(3*(p-1)-2)) * k^2
        = 3 * (k^(1*(p-1)-2)*k^2) - 3 * (k^(2*(p-1)-2)*k^2) + (k^(3*(p-1)-2)*k^2) := by ring
    rw [expand, c1, c2, c3]
    linear_combination hpoly
  have hu2 : IsUnit (k^2) := hk.pow 2
  calc k⁻¹^2 = k⁻¹^2 * k^2 * (k^2)⁻¹ := by rw [mul_assoc, ZMod.mul_inv_of_unit _ hu2, mul_one]
    _ = (3 * k^(p-3) - 3 * k^(2*p-4) + k^(3*p-5)) * k^2 * (k^2)⁻¹ := by
        rw [hkk.trans hR.symm]
    _ = _ := by rw [mul_assoc, ZMod.mul_inv_of_unit _ hu2, mul_one]

theorem isUnit_cast [Fact p.Prime] (k : ℕ) (hk : k ∈ Ico 1 p) :
    IsUnit ((k : ZMod (p^3))) := by
  haveI : NeZero (p^3) := ⟨by have := (Fact.out : p.Prime).pos; positivity⟩
  rw [mem_Ico] at hk
  have hp : p.Prime := Fact.out
  have hpk : ¬ p ∣ k := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  have hcop : Nat.Coprime k p := Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hpk)
  exact (ZMod.isUnit_iff_coprime k (p^3)).mpr (hcop.pow_right 3)

theorem fermat_cast [Fact p.Prime] (k : ℕ) (hk : k ∈ Ico 1 p) :
    (p : ZMod (p^3)) ∣ ((k : ZMod (p^3))^(p-1) - 1) := by
  rw [mem_Ico] at hk
  have hp : p.Prime := Fact.out
  have hcast : (((k:ZMod (p^3)))^(p-1) - 1) = (((k^(p-1) - 1 : ℕ)):ZMod (p^3)) := by
    have h1 : 1 ≤ k^(p-1) := Nat.one_le_pow _ _ (by omega)
    push_cast [Nat.cast_sub h1]; ring
  rw [hcast]
  have hpk : ¬ p ∣ k := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  have hcop : Nat.Coprime k p := Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hpk)
  have hmod : k^(p-1) ≡ 1 [MOD p] := by
    have := Nat.ModEq.pow_totient hcop
    rwa [Nat.totient_prime hp] at this
  have hdvd : p ∣ (k^(p-1) - 1) := by
    have h1 : 1 ≤ k^(p-1) := Nat.one_le_pow _ _ (by omega)
    exact (Nat.modEq_iff_dvd' h1).mp hmod.symm
  obtain ⟨c, hc⟩ := hdvd
  rw [hc]; push_cast; exact ⟨c, by ring⟩

/-- The H2 inverse-power identity in `ZMod (p^3)`. -/
theorem H2_eq [Fact p.Prime] (hp : 5 ≤ p) :
    H2 p = 3 * S p (p-3) - 3 * S p (2*p-4) + S p (3*p-5) := by
  unfold H2 S
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact inv_sq_term hp _ (isUnit_cast k hk) (fermat_cast k hk)

end Key
