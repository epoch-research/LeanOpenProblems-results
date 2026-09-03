import Submission.HighCountProductFailure

/-! Fixed positive multipliers cannot transfer all high-count quartic targets
at any power congruent to three modulo four. This is a restriction on an
amplification strategy, not a bound on the unrestricted representation count. -/
namespace Erdos322Research.QuarticOddPowerFailure
noncomputable section
open QuarticSquareMultiplier QuarticProgressionPeaks HighCountProductFailure
open QuarticScaledRationalProduct
set_option Elab.async false

private lemma cube_residue_test (c : Fin 16) (hc : c.val ≠ 0) :
    ∃ a : Fin 4, 0 < a.val ∧ 4 < (c.val*a.val^3)%16 := by
  revert c
  decide +kernel

/-- Every fixed positive integer multiplier fails to preserve rational
representability on infinitely many high-count targets under cubing. -/
theorem infinitely_many_cube_failures (C M : ℕ) (hC : 0 < C) :
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
      rw [← mul_assoc,he]
    · have hc : C%16 ≠ 0 := fun hh ↦ hd (Nat.dvd_of_mod_eq_zero hh)
      obtain ⟨a,ha,hbad⟩ := cube_residue_test
        ⟨C%16,Nat.mod_lt _ (by decide)⟩ hc
      apply (infinitely_many_large_counts_in_progression 16 a.val M
        (by decide) (small_residue_represented a)).mono
      rintro n ⟨hn,hcount⟩
      refine ⟨hcount,?_⟩
      intro hh
      have hmod := represented_mod_sixteen hh
      have he : (C*n^3)%16=((C%16)*a.val^3)%16 := by
        have hn' : n%16=a.val%16 := hn
        simp only [Nat.mul_mod,Nat.pow_mod,hn',Nat.mod_mod]
      rw [he] at hmod
      change 4 < ((C%16)*a.val^3)%16 at hbad
      exact Nat.not_lt_of_ge hmod hbad

/-- Removing an arbitrary nonzero fourth-power scale preserves rational
representability. No integrality of the representation is asserted. -/
lemma represented_cancel_fourth (A d : ℕ) (hd : d ≠ 0)
    (h : Represented (A*d^4)) : Represented A := by
  obtain ⟨a,ha⟩ := h
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  refine ⟨fun i ↦ a i/(d : ℚ),?_⟩
  simp only [div_pow,← Finset.sum_div,ha,Nat.cast_mul,Nat.cast_pow]
  exact mul_div_cancel_right₀ (A : ℚ) (pow_ne_zero 4 hd')

/-- The cubing obstruction also rules out all powers `4*m+3`, at arbitrarily
large source multiplicities and infinitely many distinct source targets. -/
theorem infinitely_many_power_failures (C M m : ℕ) (hC : 0 < C) :
    {n : ℕ | M < Erdos322.representationCount 4 n ∧
      ¬ Represented (C*n^(4*m+3))}.Infinite := by
  apply (infinitely_many_cube_failures C M hC).mono
  rintro n ⟨hn,hbad⟩
  refine ⟨hn,?_⟩
  intro hh
  have hn0 : n ≠ 0 := by
    intro hz
    apply hbad
    subst n
    exact ⟨0,by simp⟩
  apply hbad
  apply represented_cancel_fourth (C*n^3) (n^m) (pow_ne_zero _ hn0)
  convert hh using 1
  rw [← pow_mul,show m*4=4*m by omega,pow_add]
  ring

/-- The obstruction is unchanged for rational multipliers, because a fixed
fourth-power scaling clears their denominators. -/
theorem infinitely_many_rational_power_failures (C : ℚ) (hC : 0 < C) (M m : ℕ) :
    {n : ℕ | M < Erdos322.representationCount 4 n ∧
      ¬ (∃ a : Fin 4 → ℚ, ∑ i, a i^4=C*(n : ℚ)^(4*m+3))}.Infinite := by
  obtain ⟨d,K,hd,hK,hscale⟩ := natural_fourth_multiple C hC
  apply (infinitely_many_power_failures K M m hK).mono
  rintro n ⟨hn,hbad⟩
  refine ⟨hn,?_⟩
  rintro ⟨a,ha⟩
  apply hbad
  refine ⟨fun i ↦ (d : ℚ)*a i,?_⟩
  simp only [mul_pow,← Finset.mul_sum,ha,Nat.cast_mul,Nat.cast_pow,hscale]
  ring

/-- Even an arbitrary choice rule, rather than a polynomial or rational
formula, cannot transfer every target above a fixed count threshold in this
way. This does not restrict rules applicable only to a selected family. -/
theorem no_high_count_power_transfer (C : ℚ) (hC : 0 < C) (M m : ℕ) :
    ¬ (∀ n : ℕ, M < Erdos322.representationCount 4 n →
      ∃ a : Fin 4 → ℚ, ∑ i, a i^4=C*(n : ℚ)^(4*m+3)) := by
  intro h
  obtain ⟨n,hn,hbad⟩ := (infinitely_many_rational_power_failures C hC M m).nonempty
  exact hbad (h n hn)

/-- A generic rational-function norm formula at these exponents is impossible,
even if its displayed denominator vanishes at the obstructing input. -/
theorem no_rational_power_formula (C : ℚ) (hC : 0 < C) (m : ℕ)
    (P : Fin 4 → MvPolynomial (Fin 4) ℚ) (D : MvPolynomial (Fin 4) ℚ)
    (hD : D ≠ 0) :
    ¬ (∑ i, P i^4 = D^4 * (MvPolynomial.C C *
      (∑ j : Fin 4, MvPolynomial.X j^4)^(4*m+3))) := by
  intro h
  obtain ⟨n,hn,hbad⟩ := (infinitely_many_rational_power_failures C hC 0 m).nonempty
  obtain ⟨a,ha⟩ := Finset.card_pos.mp hn
  have ha' : ∑ i, (a i : ℕ)^4 = n := (Finset.mem_filter.mp ha).2
  have haq : ∑ i, ((a i : ℕ) : ℚ)^4 = (n : ℚ) := by exact_mod_cast ha'
  obtain ⟨b,hb⟩ := QuarticRationalSpecialization.multivariate_specialization P D
    (MvPolynomial.C C * (∑ j : Fin 4, MvPolynomial.X j^4)^(4*m+3))
    hD h (fun j ↦ ((a j : ℕ) : ℚ))
  apply hbad
  refine ⟨b,?_⟩
  simpa only [map_mul,map_pow,map_sum,MvPolynomial.eval_C,MvPolynomial.eval_X,haq]
    using hb

end
end Erdos322Research.QuarticOddPowerFailure
