import Submission.LocalSeedLifting

/-! Uniform local concentration also holds at power-permutation primes.
In particular this supplies the odd-exponent counterpart to the even seed bound. -/
namespace Erdos322Research.LocalOddSeedDensity
noncomputable section
open Finset LocalPeakCounting LocalSeedDensity LocalSeedLifting
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

/-- Coprimality with the multiplicative-group order makes powering a
permutation of the entire finite field, including zero. -/
theorem field_power_bijective (p K : ℕ) [Fact p.Prime] (hK : 0 < K)
    (hcop : (p-1).Coprime K) : Function.Bijective (fun x : ZMod p ↦ x^K) := by
  have hc : (Nat.card (ZMod p)ˣ).Coprime K := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using hcop
  have hu : Function.Bijective (fun x : (ZMod p)ˣ ↦ x^K) := hc.pow_left_bijective
  constructor
  · intro x y h
    change x^K = y^K at h
    by_cases hx : x = 0
    · subst x
      have hy : y = 0 := eq_zero_of_pow_eq_zero (by simpa only [zero_pow hK.ne'] using h.symm)
      exact hy.symm
    · have hy : y ≠ 0 := by
        intro hy
        rw [hy, zero_pow hK.ne'] at h
        exact hx (eq_zero_of_pow_eq_zero h)
      have hh : (Units.mk0 x hx)^K = (Units.mk0 y hy)^K := Units.ext h
      exact congrArg Units.val (hu.1 hh)
  · intro y
    by_cases hy : y = 0
    · exact ⟨0, by simp [hy, hK.ne']⟩
    · obtain ⟨x,hx⟩ := hu.2 (Units.mk0 y hy)
      exact ⟨x.val, congrArg Units.val hx⟩

/-- At a power-permutation prime every choice of tail coordinates has a
unique first coordinate. Only the lower bound is needed here. -/
theorem permutation_root_count_lower (k p : ℕ) [Fact p.Prime]
    (hcop : (p-1).Coprime (k+2)) : p^(k+1) ≤ rootCount (k+2) p := by
  let E := Equiv.ofBijective (fun x : ZMod p ↦ x^(k+2))
    (field_power_bijective p (k+2) (by omega) hcop)
  let f : (Fin (k+1) → ZMod p) → RingRoots (k+2) (ZMod p) := fun t ↦
    ⟨Fin.cons (E.symm (-∑ j, t j^(k+2))) t, by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have hh := E.apply_symm_apply (-∑ j, t j^(k+2))
      change (E.symm (-∑ j, t j^(k+2)))^(k+2) = -∑ j, t j^(k+2) at hh
      rw [hh, neg_add_cancel]⟩
  have hf : Function.Injective f := by
    intro t u h
    funext j
    exact congrArg (fun x : RingRoots (k+2) (ZMod p) ↦ x.val j.succ) h
  have hh := Fintype.card_le_of_injective f hf
  have heq := Fintype.card_congr (rootsEquiv (k+2) p)
  simpa only [rootCount, heq, Fintype.card_fun, Fintype.card_fin, ZMod.card] using hh

theorem permutation_first_seed_density (k p : ℕ) [Fact p.Prime]
    (hcop : (p-1).Coprime (k+2)) : p^(k+1) ≤ (2*(k+2))*firstSeedCount k p := by
  have h1 := permutation_root_count_lower k p hcop
  have h2 := root_count_le_first_seeds k p
  have h3 : 2 ≤ p^(k+1) :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_pow (by omega))
  nlinarith

/-- Uniform local concentration at power-permutation primes; its loss depends
only on the exponent, not on the size of the prime. -/
theorem uniform_permutation_local_density (p k : ℕ) [Fact p.Prime]
    (hk : ¬p ∣ k+2) (hcop : (p-1).Coprime (k+2)) (d : ℕ) :
    (d+1)*(p^((k+2)*d+1))^(k+1) ≤
      (2*(k+2))*rootCount (k+2) (p^((k+2)*d+1)) := by
  have hs := permutation_first_seed_density k p hcop
  have hg := rootCount_seed_growth p k hk d
  calc
    (d+1)*(p^((k+2)*d+1))^(k+1) =
        (d+1)*p^(k+1)*p^((k+2)*d*(k+1)) := by
      rw [← pow_mul,show ((k+2)*d+1)*(k+1)=(k+1)+(k+2)*d*(k+1) by ring,pow_add]
      ring
    _ ≤ (d+1)*((2*(k+2))*firstSeedCount k p)*p^((k+2)*d*(k+1)) := by gcongr
    _ = (2*(k+2))*((d+1)*firstSeedCount k p*p^((k+2)*d*(k+1))) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hg

end
end Erdos322Research.LocalOddSeedDensity
