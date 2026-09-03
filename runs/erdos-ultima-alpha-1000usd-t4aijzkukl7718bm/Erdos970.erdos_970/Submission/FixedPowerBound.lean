import Submission.BlockPartition
import Submission.BlockArithmetic

/-!
An unconditional fixed-power upper bound obtained from the finite block sieve.
The exponent is deliberately coarse; this does not prove the quadratic conjecture.
-/
namespace Erdos970.BlockSieve

/-- No union of one residue class for each of at most `k` primes covers a longer interval. -/
theorem cover_length_le_fixed_power (k : ℕ) (hk : 0 < k)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hcard : P.card ≤ k)
    (r : ℕ → ℕ) (m : ℕ) (hcover : ∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p]) :
    m ≤ (k + 1) ^ 632 := by
  classical
  let L := Nat.clog 2 (k + 1)
  let J := Nat.clog 2 L
  let B := primeBlock P J
  have hcut : k + 1 ≤ 2 ^ (2 ^ J) :=
    (Nat.le_pow_clog (by decide) (k + 1)).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_pow_clog (by decide) L))
  have hB (j : Fin (J + 1)) (p : ℕ) (hp : p ∈ B j) : p.Prime :=
    hP p (primeBlock_subset P J j hp)
  have hBcard : (Finset.univ.biUnion B).card ≤ k := by
    simpa only [B, primeBlock_union] using hcard
  have hmass (j : Fin (J + 1)) : (∑ p ∈ B j, (1 : ℝ) / p) ≤ 4 := by
    by_cases hj : j.val < J
    · exact primeBlock_mass_small P J hP j hj
    · have heq : j = Fin.last J := Fin.ext (by simp only [Fin.val_last]; omega)
      rw [heq]
      exact (primeBlock_mass_last P J k hP hcard hcut).trans (by norm_num)
  have hcov : ∀ x < m, ∃ j : Fin (J + 1), ∃ p ∈ B j, x ≡ r p [MOD p] := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := hcover x hx
    rw [← primeBlock_union P J] at hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact ⟨j, p, hpj, hxp⟩
  have hc := cover_bound_of_blocks (J + 1) k B (fun j => J - j.val) hB
    (primeBlock_disjoint P J) hBcard hmass (geometric_error_sum J) r m hcov
  have hcost : (∏ j, ((B j).card + 1) ^ (2 * (J - j.val + 18) + 1)) ≤ (k + 1) ^ 624 :=
    block_cost_product_le k hk (fun j => (B j).card + 1) (primeBlock_card_bound P J k hP hcard hcut)
  have hpref : (J + 2) * (k + 1) * 2 ^ (J + 2) ≤ (k + 1) ^ 8 := block_prefactor_le k hk
  calc
    m ≤ ((J + 2) * (k + 1) * 2 ^ (J + 2)) *
        ∏ j, ((B j).card + 1) ^ (2 * (J - j.val + 18) + 1) := hc
    _ ≤ (k + 1) ^ 8 * (k + 1) ^ 624 := Nat.mul_le_mul hpref hcost
    _ = (k + 1) ^ 632 := by rw [← pow_add]

/-- A uniform polynomial bound with a fixed, explicit exponent. -/
theorem isJacobsthalBound_fixed_power (k : ℕ) : IsJacobsthalBound k ((k + 1) ^ 633) := by
  by_cases hk : 0 < k
  · by_contra hbad
    obtain ⟨P, hP, hcard, r, hcover⟩ :=
      (not_isJacobsthalBound_iff_cover k ((k + 1) ^ 633)).mp hbad
    have hc := cover_length_le_fixed_power k hk P hP hcard r ((k + 1) ^ 633) hcover
    exact (Nat.pow_lt_pow_right (by omega : 1 < k + 1) (by decide : 632 < 633)).not_ge hc
  · have hk0 : k = 0 := by omega
    subst k
    simpa using isJacobsthalBound_factorial 0

theorem jacobsthalFunction_le_fixed_power (k : ℕ) :
    jacobsthalFunction k ≤ (k + 1) ^ 633 :=
  (jacobsthalFunction_le_iff k _).mpr (isJacobsthalBound_fixed_power k)

#print axioms cover_length_le_fixed_power
#print axioms jacobsthalFunction_le_fixed_power
end Erdos970.BlockSieve
