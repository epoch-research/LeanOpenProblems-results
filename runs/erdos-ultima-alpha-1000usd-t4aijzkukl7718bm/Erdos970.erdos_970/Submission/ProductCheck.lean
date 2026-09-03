import FormalConjecturesUtil

/-! A counterexample to a proposed fixed-modulus deletion recurrence, not to Erdős 970. -/

namespace Erdos970.ProductCheck

/-- A fixed-modulus analogue of `IsJacobsthalBound`. -/
def IntervalBound (n m : ℕ) : Prop :=
  ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n

/-- Four primes, all at least five, cannot cover five consecutive positions. -/
theorem intervalBound_5005 : IntervalBound 5005 5 := by
  classical
  intro a
  by_contra h
  push_neg at h
  have hex (i : Fin 5) : ∃ p : (5005 : ℕ).primeFactors, (p.val : ℤ) ∣ a + i.val := by
    obtain ⟨p, hp, hpa, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp (h i.val i.isLt)
    exact ⟨⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpn, by norm_num⟩⟩,
      Int.natCast_dvd.mpr hpa⟩
  choose f hf using hex
  have hfac : (5005 : ℕ).primeFactors = {5, 7, 11, 13} := by
    have hprod : (∏ p ∈ ({5, 7, 11, 13} : Finset ℕ), p) = 5005 := by norm_num
    rw [← hprod]
    apply Nat.primeFactors_prod
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  have hlarge (p : (5005 : ℕ).primeFactors) : 5 ≤ p.val := by
    have hp := p.property
    simp only [hfac, Finset.mem_insert, Finset.mem_singleton] at hp
    omega
  have hinj : Function.Injective f := by
    intro i j hij
    have hi := hf i
    have hj : ((f i).val : ℤ) ∣ a + j.val := by simpa only [hij] using hf j
    have hd : ((f i).val : ℤ) ∣ (j.val : ℤ) - i.val := by
      convert dvd_sub hj hi using 1; ring
    have hm : i.val ≡ j.val [MOD (f i).val] := Nat.modEq_of_dvd hd
    apply Fin.ext
    exact hm.eq_of_lt_of_lt (i.isLt.trans_le (hlarge (f i)))
      (j.isLt.trans_le (hlarge (f i)))
  have hc := Fintype.card_le_of_injective f hinj
  have hcard : (5005 : ℕ).primeFactors.card = 4 := by rw [hfac]; decide
  simp only [Fintype.card_fin, Fintype.card_coe, hcard] at hc
  omega

/-- The ten integers from `2778` through `2787` are all covered after adding the prime `3`. -/
theorem not_intervalBound_15015 : ¬IntervalBound 15015 10 := by
  intro h
  obtain ⟨i, hi, hc⟩ := h 2778
  interval_cases i <;> norm_num at hc

/-- Adding a single new prime need not at most double the fixed-modulus bound. -/
theorem deletion_doubling_false :
    ¬ (∀ n p g : ℕ, p.Prime → p.Coprime n →
      IntervalBound n g → IntervalBound (p * n) (2 * g)) := by
  intro h
  exact not_intervalBound_15015 (h 5005 3 5 (by norm_num) (by norm_num) intervalBound_5005)

#print axioms deletion_doubling_false
end Erdos970.ProductCheck
