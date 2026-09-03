import Submission.HighCountProductFailure

/-! Fixed-scale amplification to exponents congruent to three modulo four
fails at arbitrarily high exact quartic counts. This is not a bound on those
counts and does not settle Erdős 322. -/
namespace Erdos322Research.QuarticCubingAmplificationFailure
noncomputable section
open QuarticSquareMultiplier QuarticScaledRationalProduct
open QuarticProgressionPeaks HighCountProductFailure
set_option Elab.async false
set_option maxHeartbeats 1000000

private lemma residue_cube (c : Fin 16) (hc : c.val ≠ 0) :
    ∃ a : Fin 4, 0 < a.val ∧ 4 < (c.val*a.val^3)%16 := by
  revert c
  decide +kernel

/-- Every fixed positive natural scale fails on infinitely many targets
above any prescribed count threshold. Arbitrary rational output coordinates
are already excluded. -/
theorem infinitely_many_bad_cubes (C M : ℕ) (hC : 0 < C) :
    {n : ℕ | M < Erdos322.representationCount 4 n ∧
      ¬ Represented (C*n^3)}.Infinite := by
  induction C using Nat.strong_induction_on with
  | h C ih =>
    by_cases hd : 16 ∣ C
    · have hp : 0 < C/16 := Nat.div_pos (Nat.le_of_dvd hC hd) (by decide)
      have hs : C/16 < C := Nat.div_lt_self hC (by decide)
      have he : 16*(C/16)=C := Nat.mul_div_cancel' hd
      apply (ih (C/16) hs hp).mono
      rintro n ⟨hn,hbad⟩
      refine ⟨hn,fun hh ↦ hbad ?_⟩
      apply represented_strip_sixteen
      convert hh using 1
      calc
        16*(C/16*n^3) = (16*(C/16))*n^3 := by ring
        _ = C*n^3 := by rw [he]
    · have hc : C%16 ≠ 0 := fun hh ↦ hd (Nat.dvd_of_mod_eq_zero hh)
      obtain ⟨a,ha,hab⟩ := residue_cube ⟨C%16,Nat.mod_lt _ (by decide)⟩ hc
      apply (infinitely_many_large_counts_in_progression 16 a.val M (by decide)
        (small_residue_represented a)).mono
      rintro n ⟨hn,hcount⟩
      refine ⟨hcount,?_⟩
      intro hh
      have hm := represented_mod_sixteen hh
      have hna : n%16=a.val%16 := hn
      have he : (C*n^3)%16=((C%16)*a.val^3)%16 := by
        simp only [Nat.mul_mod,Nat.pow_mod,hna,Nat.mod_mod]
      rw [he] at hm
      change 4 < ((C%16)*a.val^3)%16 at hab
      omega

private lemma represented_strip_fourth {m n : ℕ} (hn : n ≠ 0)
    (h : Represented (m*n^4)) : Represented m := by
  obtain ⟨a,ha⟩ := h
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  refine ⟨fun i ↦ a i/(n : ℚ),?_⟩
  simp only [div_pow,← Finset.sum_div,ha,Nat.cast_mul,Nat.cast_pow]
  exact mul_div_cancel_right₀ _ (pow_ne_zero 4 hnq)

/-- The same obstruction applies to every exponent `4*j+3`. -/
theorem infinitely_many_bad_powers (C M j : ℕ) (hC : 0 < C) :
    {n : ℕ | M < Erdos322.representationCount 4 n ∧
      ¬ Represented (C*n^(4*j+3))}.Infinite := by
  apply (infinitely_many_bad_cubes C M hC).mono
  rintro n ⟨hcount,hbad⟩
  refine ⟨hcount,?_⟩
  have hn : n ≠ 0 := by
    intro hz
    subst n
    apply hbad
    exact ⟨fun _ ↦ 0,by simp⟩
  intro hh
  apply hbad
  apply represented_strip_fourth (pow_ne_zero j hn)
  convert hh using 1
  rw [pow_add,pow_mul]
  ring

/-- Clearing a fourth-power denominator extends the failure to every fixed
positive rational scale. No restriction on a proposed choice rule or formula
is assumed. -/
theorem infinitely_many_bad_rational_powers (C : ℚ) (hC : 0 < C) (M j : ℕ) :
    {n : ℕ | M < Erdos322.representationCount 4 n ∧
      ¬ (∃ a : Fin 4 → ℚ, ∑ i, a i^4=C*(n : ℚ)^(4*j+3))}.Infinite := by
  obtain ⟨d,K,hd,hK,hscale⟩ := natural_fourth_multiple C hC
  apply (infinitely_many_bad_powers K M j hK).mono
  rintro n ⟨hcount,hbad⟩
  refine ⟨hcount,?_⟩
  rintro ⟨a,ha⟩
  apply hbad
  refine ⟨fun i ↦ (d : ℚ)*a i,?_⟩
  simp only [mul_pow,← Finset.mul_sum,ha,Nat.cast_mul,Nat.cast_pow,hscale]
  ring

end
end Erdos322Research.QuarticCubingAmplificationFailure
