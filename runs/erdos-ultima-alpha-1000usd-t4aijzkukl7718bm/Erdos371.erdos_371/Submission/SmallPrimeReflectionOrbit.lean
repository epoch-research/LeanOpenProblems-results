import Submission.SmallPrimeReflection

/-! Orbit structure of the least-losing-prime reflection. These results concern
iteration of a noninjective map, not natural density of its input signs. -/
namespace Erdos371

lemma primeWinner_prime_of_one_lt (n : ℕ) (hn : 1 < n) :
    (primeWinner n).Prime := by
  rcases primeWinner_prime_or_one n with hp | hp
  · exact hp
  · have h := (leastLosingPrime_prime n hn).two_le
    have h' := leastLosingPrime_lt_winner n hn
    omega

lemma smallPrimeReflection_mod_free (n : ℕ)
    (hn : n < leastLosingPrime n * primeWinner n) :
    smallPrimeReflection n = leastLosingPrime n * primeWinner n - 1 - n := by
  simp only [smallPrimeReflection, divisorReflection, Nat.mod_eq_of_lt hn]

lemma losingNumber_reflection_add_mod_free (n : ℕ) (hn : 1 < n)
    (hsmall : n < leastLosingPrime n * primeWinner n) :
    losingNumber n + losingNumber (smallPrimeReflection n) =
      leastLosingPrime n * primeWinner n := by
  have he := smallPrimeReflection_mod_free n hsmall
  have hs := (smallPrimeReflection_structure n hn).1
  unfold losingNumber
  simp only [hs]
  rcases lt_or_gt_of_ne (consecutive_maxPrimeFac_ne n) with h | h <;>
    simp only [h, h.not_gt, if_true, if_false] <;> omega

/-- Inside the divisor-product period, an odd least losing prime is sent to
2. The modulo reduction must not be omitted from this hypothesis. -/
theorem leastLosingPrime_small_reflection_eq_two (n : ℕ) (hn : 1 < n)
    (hsmall : n < leastLosingPrime n * primeWinner n) :
    leastLosingPrime (smallPrimeReflection n) = 2 := by
  by_cases htwo : leastLosingPrime n = 2
  · have hle := leastLosingPrime_reflection_le n hn
    have hge := (leastLosingPrime_prime _ (smallPrimeReflection_bounds n hn).1).two_le
    omega
  have hlodd := (leastLosingPrime_prime n hn).eq_two_or_odd.resolve_left htwo
  have hpodd := (primeWinner_prime_of_one_lt n hn).eq_two_or_odd.resolve_left
    (show primeWinner n ≠ 2 by
      have := leastLosingPrime_lt_winner n hn
      have := (leastLosingPrime_prime n hn).two_le
      omega)
  have hnodd : losingNumber n % 2 = 1 := by
    have hnot : ¬2 ∣ losingNumber n := by
      simpa only [leastLosingPrime, Nat.minFac_eq_two_iff] using htwo
    omega
  have hs := congrArg (fun m : ℕ => m % 2)
    (losingNumber_reflection_add_mod_free n hn hsmall)
  dsimp only at hs
  rw [Nat.add_mod, Nat.mul_mod, hlodd, hpodd, hnodd] at hs
  apply (Nat.minFac_eq_two_iff _).mpr
  exact Nat.dvd_of_mod_eq_zero (by omega)

/-- Either the least losing prime strictly decreases, or within two steps
it becomes 2. -/
theorem leastLosingPrime_reflection_descent (n : ℕ) (hn : 1 < n) :
    leastLosingPrime (smallPrimeReflection n) < leastLosingPrime n ∨
      leastLosingPrime (smallPrimeReflection (smallPrimeReflection n)) = 2 := by
  have hle := leastLosingPrime_reflection_le n hn
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inl hlt
  · right
    apply leastLosingPrime_small_reflection_eq_two _ (smallPrimeReflection_bounds n hn).1
    rw [heq, (smallPrimeReflection_structure n hn).2]
    exact (smallPrimeReflection_bounds n hn).2

/-- A finite bound on the time to reach an even losing number. It does not
control the multiplicity of the map or the distribution of hitting-time parity. -/
theorem smallPrimeReflection_reaches_least_two (n : ℕ) (hn : 1 < n) :
    ∃ k ≤ 2 * leastLosingPrime n, leastLosingPrime (smallPrimeReflection^[k] n) = 2 := by
  generalize he : leastLosingPrime n = l
  induction l using Nat.strong_induction_on generalizing n with
  | h l ih =>
    by_cases ht : l = 2
    · exact ⟨0, by omega, by simpa only [Function.iterate_zero_apply] using he.trans ht⟩
    rcases leastLosingPrime_reflection_descent n hn with hdec | htwo
    · obtain ⟨k, hk, hk2⟩ := ih (leastLosingPrime (smallPrimeReflection n))
        (by omega) (smallPrimeReflection n) (smallPrimeReflection_bounds n hn).1 rfl
      refine ⟨k + 1, by omega, ?_⟩
      simpa only [Function.iterate_succ_apply] using hk2
    · refine ⟨2, ?_, ?_⟩
      · have := (leastLosingPrime_prime n hn).two_le
        omega
      · simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using htwo


lemma leastLosingPrime_reflection_eq_two_of_eq_two (n : ℕ) (hn : 1 < n)
    (htwo : leastLosingPrime n = 2) :
    leastLosingPrime (smallPrimeReflection n) = 2 := by
  have hle := leastLosingPrime_reflection_le n hn
  have hge := (leastLosingPrime_prime _ (smallPrimeReflection_bounds n hn).1).two_le
  omega

/-- Once the losing number is even, the next image is one of the two
canonical indices immediately around the winning prime. -/
theorem smallPrimeReflection_canonical_of_least_two (n : ℕ) (hn : 1 < n)
    (htwo : leastLosingPrime n = 2) :
    smallPrimeReflection n =
      if Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) then primeWinner n
      else primeWinner n - 1 := by
  have hp := primeWinner_prime_of_one_lt n hn
  have hp2 : 2 < primeWinner n := by
    have := leastLosingPrime_lt_winner n hn
    omega
  have hpodd := hp.eq_two_or_odd.resolve_left (by omega : primeWinner n ≠ 2)
  by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
  · rw [if_pos h]
    have hd2 : 2 ∣ n := by
      apply (Nat.minFac_eq_two_iff n).mp
      simpa only [leastLosingPrime, losingNumber, if_pos h] using htwo
    have hdp : primeWinner n ∣ n+1 := by
      simpa only [primeWinner, max_eq_right h.le] using
        (Nat.maxPrimeFac_dvd (n := n+1))
    have hc := (divisor_pair_coprime n 2 (primeWinner n) hd2 hdp).symm
    have he : smallPrimeReflection n = adjacentRoot (primeWinner n) 2 hc := by
      rw [smallPrimeReflection, htwo,
        divisorReflection_eq_root n 2 (primeWinner n) (by omega) hp.one_lt hd2 hdp]
    rw [he]
    exact (adjacentRoot_unique (primeWinner n) 2 hc hp.pos (by omega)
      (primeWinner n) (by omega) (dvd_refl _) (Nat.dvd_of_mod_eq_zero (by omega))).symm
  · rw [if_neg h]
    have hd2 : 2 ∣ n+1 := by
      apply (Nat.minFac_eq_two_iff (n+1)).mp
      simpa only [leastLosingPrime, losingNumber, if_neg h] using htwo
    have hdp : primeWinner n ∣ n := by
      simpa only [primeWinner, max_eq_left (not_lt.mp h)] using
        (Nat.maxPrimeFac_dvd (n := n))
    have hc := (divisor_pair_coprime n (primeWinner n) 2 hdp hd2).symm
    have he : smallPrimeReflection n = adjacentRoot 2 (primeWinner n) hc := by
      have he' : smallPrimeReflection n = divisorReflection n (primeWinner n) 2 := by
        simp only [smallPrimeReflection, divisorReflection, htwo, Nat.mul_comm]
      rw [he', divisorReflection_eq_root n (primeWinner n) 2 hp.one_lt (by omega) hdp hd2]
    rw [he]
    exact (adjacentRoot_unique 2 (primeWinner n) hc (by omega) hp.pos
      (primeWinner n - 1) (by omega) (Nat.dvd_of_mod_eq_zero (by omega))
      (by rw [Nat.sub_add_cancel hp.one_le])).symm

lemma smallPrimeReflection_iterate_pos (n k : ℕ) (hn : 1 < n) :
    1 < smallPrimeReflection^[k] n := by
  induction k with
  | zero => exact hn
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (smallPrimeReflection_bounds _ ih).1

lemma smallPrimeReflection_iterate_winner (n k : ℕ) (hn : 1 < n) :
    primeWinner (smallPrimeReflection^[k] n) = primeWinner n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',
      (smallPrimeReflection_structure _ (smallPrimeReflection_iterate_pos n k hn)).2, ih]

/-- Every orbit reaches the canonical two-cycle. The bound depends only on
the initial least losing prime, but gives no balance of the input signs. -/
theorem smallPrimeReflection_eventually_canonical (n : ℕ) (hn : 1 < n) :
    ∃ k ≤ 2 * leastLosingPrime n + 1, ∀ j ≥ k,
      (smallPrimeReflection^[j] n = primeWinner n - 1 ∨
        smallPrimeReflection^[j] n = primeWinner n) ∧
      smallPrimeReflection^[j+2] n = smallPrimeReflection^[j] n := by
  obtain ⟨k, hk, hk2⟩ := smallPrimeReflection_reaches_least_two n hn
  let y (j : ℕ) := smallPrimeReflection^[j] n
  have hy (j : ℕ) : y (j+1) = smallPrimeReflection (y j) :=
    Function.iterate_succ_apply' smallPrimeReflection j n
  have hpos (j : ℕ) : 1 < y j := smallPrimeReflection_iterate_pos n j hn
  have hwin (j : ℕ) : primeWinner (y j) = primeWinner n :=
    smallPrimeReflection_iterate_winner n j hn
  have htwo : ∀ j ≥ k, leastLosingPrime (y j) = 2 := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact hk2
    | succ j hj ih =>
      rw [hy]
      exact leastLosingPrime_reflection_eq_two_of_eq_two _ (hpos j) ih
  refine ⟨k+1, by omega, ?_⟩
  intro j hj
  have hj1 : j-1+1=j := by omega
  have hcanonical := smallPrimeReflection_canonical_of_least_two (y (j-1))
    (hpos (j-1)) (htwo (j-1) (by omega))
  rw [← hy, hj1, hwin] at hcanonical
  have hcases : y j = primeWinner n - 1 ∨ y j = primeWinner n := by
    split_ifs at hcanonical with h
    · exact Or.inr hcanonical
    · exact Or.inl hcanonical
  refine ⟨hcases, ?_⟩
  have hsmall : y j < leastLosingPrime (y j) * primeWinner (y j) := by
    rw [htwo j (by omega), hwin]
    have hp := (primeWinner_prime_of_one_lt n hn).pos
    rcases hcases with h | h <;> omega
  have hsmall' : y (j+1) < leastLosingPrime (y (j+1)) * primeWinner (y (j+1)) := by
    rw [htwo (j+1) (by omega), hwin]
    have hb := (smallPrimeReflection_bounds (y j) (hpos j)).2
    rwa [← hy, htwo j (by omega), hwin] at hb
  have he := smallPrimeReflection_mod_free (y j) hsmall
  have he' := smallPrimeReflection_mod_free (y (j+1)) hsmall'
  rw [← hy, htwo j (by omega), hwin] at he
  rw [← hy, htwo (j+1) (by omega), hwin] at he'
  change y (j+2) = y j
  rw [htwo j (by omega), hwin] at hsmall
  simp only [Nat.add_assoc, Nat.reduceAdd] at he'
  omega

/-- The canonical cycle need not be reached within two steps. This also
illustrates why one must track the least prime after each modulo reduction. -/
theorem smallPrimeReflection_three_step_example :
    smallPrimeReflection 774 = 85 ∧ smallPrimeReflection 85 = 129 ∧
      smallPrimeReflection 129 = 42 ∧ smallPrimeReflection 42 = 43 ∧
      smallPrimeReflection 43 = 42 ∧ primeWinner 774 = 43 := by
  decide +kernel

/-- Finite incoming harmonic weight. No asymptotic invariance is asserted. -/
def reflectionHarmonicFiber (N m : ℕ) : ℚ :=
  ∑ n ∈ (Finset.Ico 2 N).filter (fun n => smallPrimeReflection n = m), (1 : ℚ)/n

theorem reflectionHarmonicFiber_small_example :
    reflectionHarmonicFiber 9 3 = 5/8 ∧ reflectionHarmonicFiber 9 3 ≠ 1/3 := by
  have he : reflectionHarmonicFiber 9 3 = 5/8 := by decide +kernel
  rw [he]
  norm_num

#print axioms smallPrimeReflection_three_step_example
#print axioms reflectionHarmonicFiber_small_example
#print axioms leastLosingPrime_small_reflection_eq_two
#print axioms smallPrimeReflection_reaches_least_two
#print axioms smallPrimeReflection_canonical_of_least_two
#print axioms smallPrimeReflection_eventually_canonical
end Erdos371
