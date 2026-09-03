import Submission.PrimitiveProductCharacters

/-!
# Character-lifting errors at composite moduli

The discrepancy at a composite modulus is reduced to primitive conductor
sums plus an explicit logarithmic prime-power error. No estimate at cofinal
near-full modulus levels is asserted.
-/

open scoped Classical BigOperators
open Nat Finset ArithmeticFunction

namespace Erdos821.AnalyticSieve

noncomputable def nonunitMangoldt (d N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, if ¬n.Coprime d then vonMangoldt n else 0

noncomputable def characterLiftError (d N : ℕ) : ℝ :=
  (Nat.log 2 N : ℝ) * Real.log d

lemma characterLiftError_nonneg (d N : ℕ) : 0 ≤ characterLiftError d N :=
  mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

lemma nonunitMangoldt_nonneg (d N : ℕ) : 0 ≤ nonunitMangoldt d N := by
  apply Finset.sum_nonneg
  intro n hn
  split_ifs <;> first | exact vonMangoldt_nonneg | exact le_rfl

lemma noncoprime_prime_power_dvd_log_power {d n N : ℕ}
    (hn : IsPrimePow n) (hnN : n ≤ N) (hnd : ¬n.Coprime d) :
    n ∣ d ^ Nat.log 2 N := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  have hpd : p ∣ d := by
    by_contra h
    exact hnd ((hp.coprime_iff_not_dvd.mpr h).pow_left k)
  have hkN : k ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by decide)
    ((Nat.pow_le_pow_left hp.two_le k).trans hnN)
  exact pow_dvd_pow_of_dvd_of_le hpd hkN

/-- Only prime powers contribute. All contributing prime powers divide a
single logarithmic power of the modulus, whose divisor Mangoldt sum is known. -/
lemma nonunitMangoldt_le_liftError (d N : ℕ) (hd : d ≠ 0) :
    nonunitMangoldt d N ≤ characterLiftError d N := by
  let F := (Icc 1 N).filter (fun n => ¬n.Coprime d ∧ IsPrimePow n)
  have heq : nonunitMangoldt d N = ∑ n ∈ F, vonMangoldt n := by
    simp only [nonunitMangoldt, F, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime d
    · simp [hc]
    · by_cases hp : IsPrimePow n
      · simp only [hc, not_false_eq_true, hp, and_self, if_true]
      · simp only [hc, not_false_eq_true, hp, and_false, if_false, if_true,
          vonMangoldt_eq_zero_iff.mpr hp]
  have hsub : F ⊆ (d ^ Nat.log 2 N).divisors := by
    intro n hn
    obtain ⟨hnI, hnc, hnp⟩ := Finset.mem_filter.mp hn
    exact Nat.mem_divisors.mpr
      ⟨noncoprime_prime_power_dvd_log_power hnp (Finset.mem_Icc.mp hnI).2 hnc, pow_ne_zero _ hd⟩
  rw [heq]
  calc
    _ ≤ ∑ n ∈ (d ^ Nat.log 2 N).divisors, vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => vonMangoldt_nonneg)
    _ = Real.log ((d ^ Nat.log 2 N : ℕ) : ℝ) := vonMangoldt_sum
    _ = characterLiftError d N := by rw [Nat.cast_pow, Real.log_pow]; rfl

lemma principal_character_nat (d n : ℕ) :
    (1 : DirichletCharacter ℂ d) (n : ZMod d) = if n.Coprime d then 1 else 0 := by
  by_cases h : n.Coprime d
  · rw [if_pos h]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n d).mpr h)
  · rw [if_neg h]
    exact MulChar.map_nonunit _ ((ZMod.isUnit_iff_coprime n d).not.mpr h)

lemma twisted_principal_mangoldt_composite (d N : ℕ) :
    twistedArithmeticSum (1 : DirichletCharacter ℂ d) vonMangoldt N =
      ((mangoldtSum N - nonunitMangoldt d N : ℝ) : ℂ) := by
  simp only [twistedArithmeticSum, mangoldtSum, nonunitMangoldt, Complex.ofReal_sub,
    Complex.ofReal_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [principal_character_nat]
  by_cases h : n.Coprime d <;> simp [h]

lemma changeLevel_apply_nat {c d : ℕ} (hcd : c ∣ d)
    (ψ : DirichletCharacter ℂ c) (n : ℕ) :
    (DirichletCharacter.changeLevel hcd ψ) (n : ZMod d) =
      if n.Coprime d then ψ (n : ZMod c) else 0 := by
  by_cases hn : n.Coprime d
  · rw [if_pos hn]
    have hu : IsUnit (n : ZMod d) := (ZMod.isUnit_iff_coprime n d).mpr hn
    have h := ψ.changeLevel_eq_cast_of_dvd hcd hu.unit
    simpa only [hu.unit_spec, ZMod.cast_natCast hcd] using h
  · rw [if_neg hn]
    exact MulChar.map_nonunit _ ((ZMod.isUnit_iff_coprime n d).not.mpr hn)

lemma norm_twisted_changeLevel_sub_le_nonunit {c d : ℕ} (hcd : c ∣ d)
    (ψ : DirichletCharacter ℂ c) (N : ℕ) :
    ‖twistedArithmeticSum (DirichletCharacter.changeLevel hcd ψ) vonMangoldt N -
      twistedArithmeticSum ψ vonMangoldt N‖ ≤ nonunitMangoldt d N := by
  rw [twistedArithmeticSum, twistedArithmeticSum, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  change ‖(vonMangoldt n : ℂ) * (DirichletCharacter.changeLevel hcd ψ) (n : ZMod d) -
    (vonMangoldt n : ℂ) * ψ (n : ZMod c)‖ ≤ if ¬n.Coprime d then vonMangoldt n else 0
  rw [changeLevel_apply_nat]
  by_cases hc : n.Coprime d
  · rw [if_pos hc, if_neg (not_not.mpr hc), sub_self, norm_zero]
  · simp only [hc, not_false_eq_true, if_true, if_false, mul_zero, zero_sub, norm_neg,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (ψ.norm_le_one _) vonMangoldt_nonneg

lemma norm_twisted_changeLevel_le {c d : ℕ} (hcd : c ∣ d) (hd : d ≠ 0)
    (ψ : DirichletCharacter ℂ c) (N : ℕ) :
    ‖twistedArithmeticSum (DirichletCharacter.changeLevel hcd ψ) vonMangoldt N‖ ≤
      ‖twistedArithmeticSum ψ vonMangoldt N‖ + characterLiftError d N := by
  have h := norm_le_norm_sub_add
    (twistedArithmeticSum (DirichletCharacter.changeLevel hcd ψ) vonMangoldt N)
    (twistedArithmeticSum ψ vonMangoldt N)
  calc
    _ ≤ ‖twistedArithmeticSum (DirichletCharacter.changeLevel hcd ψ) vonMangoldt N -
        twistedArithmeticSum ψ vonMangoldt N‖ + ‖twistedArithmeticSum ψ vonMangoldt N‖ := h
    _ ≤ characterLiftError d N + ‖twistedArithmeticSum ψ vonMangoldt N‖ :=
      add_le_add ((norm_twisted_changeLevel_sub_le_nonunit hcd ψ N).trans
        (nonunitMangoldt_le_liftError d N hd)) le_rfl
    _ = _ := add_comm _ _

lemma character_eq_lift_primitive {d : ℕ} (χ : DirichletCharacter ℂ d) :
    χ = DirichletCharacter.changeLevel χ.conductor_dvd_level χ.primitiveCharacter := by
  exact Classical.choose_spec χ.factorsThrough_conductor.choose_spec

/-- Primitive sums at all possible nontrivial conductors of the modulus. -/
noncomputable def primitiveConductorMangoldtMajorant (d N : ℕ) : ℝ :=
  ∑ c ∈ d.divisors.erase 1, ∑ ψ ∈ Erdos821.primitiveCharacters c,
    ‖twistedArithmeticSum ψ vonMangoldt N‖

lemma nonprincipal_conductor_mem {d : ℕ} (hd : d ≠ 0)
    {χ : DirichletCharacter ℂ d} (hχ : χ ∈ nonprincipalCharacters d) :
    χ.conductor ∈ d.divisors.erase 1 := by
  have hχne : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
  have hc1 : χ.conductor ≠ 1 := by
    intro hc
    exact hχne ((DirichletCharacter.eq_one_iff_conductor_eq_one hd).mpr hc)
  exact Finset.mem_erase.mpr ⟨hc1, Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, hd⟩⟩

/-- Cover the nonprincipal characters by lifts of primitive characters at
nontrivial divisors. The prime-power error is bounded using sum phi(c)=d;
no conductor-preservation or disjointness assertion is needed for the cover. -/
theorem nonprincipal_mangoldt_sum_le_conductors (d N : ℕ) (hd : d ≠ 0) :
    (∑ χ ∈ nonprincipalCharacters d, ‖twistedArithmeticSum χ vonMangoldt N‖) ≤
      primitiveConductorMangoldtMajorant d N + (d : ℝ) * characterLiftError d N := by
  let C := d.divisors.erase 1
  let Z := (Σ c : {c : ℕ // c ∈ C}, DirichletCharacter ℂ c.val)
  let F : Finset Z := C.attach.sigma (fun c => Erdos821.primitiveCharacters c.val)
  let lift : Z → DirichletCharacter ℂ d := fun z =>
    DirichletCharacter.changeLevel (Nat.dvd_of_mem_divisors (Finset.mem_erase.mp z.1.property).2) z.2
  have hcover : nonprincipalCharacters d ⊆ F.image lift := by
    intro χ hχ
    have hc : χ.conductor ∈ C := nonprincipal_conductor_mem hd hχ
    refine Finset.mem_image.mpr ⟨⟨⟨χ.conductor, hc⟩, χ.primitiveCharacter⟩, ?_, ?_⟩
    · exact Finset.mem_sigma.mpr ⟨Finset.mem_attach _ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, χ.primitiveCharacter_isPrimitive⟩⟩
    · exact (character_eq_lift_primitive χ).symm
  have hmass : (∑ c ∈ C, ((Erdos821.primitiveCharacters c).card : ℝ)) ≤ d := by
    have hNat : (∑ c ∈ C, (Erdos821.primitiveCharacters c).card) ≤ d := by
      calc
        _ ≤ ∑ c ∈ C, c.totient := by
          apply Finset.sum_le_sum
          intro c hc
          have hc0 := Nat.pos_of_mem_divisors (Finset.mem_erase.mp hc).2
          have h := Erdos821.primitiveCharacters_card_add_imprimitive c hc0.ne'
          omega
        _ ≤ ∑ c ∈ d.divisors, c.totient :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun c _ _ => Nat.zero_le _)
        _ = d := Nat.sum_totient d
    exact_mod_cast hNat
  calc
    _ ≤ ∑ χ ∈ F.image lift, ‖twistedArithmeticSum χ vonMangoldt N‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun χ _ _ => norm_nonneg _)
    _ ≤ ∑ z ∈ F, ‖twistedArithmeticSum (lift z) vonMangoldt N‖ :=
      Finset.sum_image_le_of_nonneg (fun χ _ => norm_nonneg _)
    _ ≤ ∑ z ∈ F, (‖twistedArithmeticSum z.2 vonMangoldt N‖ + characterLiftError d N) := by
      apply Finset.sum_le_sum
      intro z hz
      exact norm_twisted_changeLevel_le _ hd z.2 N
    _ = primitiveConductorMangoldtMajorant d N +
        (∑ c ∈ C, ((Erdos821.primitiveCharacters c).card : ℝ)) * characterLiftError d N := by
      dsimp only [F]
      rw [Finset.sum_sigma]
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]
      rw [Finset.sum_attach C (fun c => ∑ ψ ∈ Erdos821.primitiveCharacters c,
        ‖twistedArithmeticSum ψ vonMangoldt N‖),
        Finset.sum_attach C (fun c => ((Erdos821.primitiveCharacters c).card : ℝ))]
      rfl
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hmass (characterLiftError_nonneg d N))

lemma composite_progression_discrepancy_all_characters (d N : ℕ) [NeZero d] :
    |residueOneMangoldt d N - mangoldtSum N / d.totient| ≤
      ((∑ χ ∈ nonprincipalCharacters d, ‖twistedArithmeticSum χ vonMangoldt N‖) +
        nonunitMangoldt d N) / d.totient := by
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos d)
  have h := Finset.sum_erase_add (univ : Finset (DirichletCharacter ℂ d))
    (fun χ => twistedArithmeticSum χ vonMangoldt N) (mem_univ 1)
  dsimp only at h
  rw [residueOneMangoldt_orthogonality, twisted_principal_mangoldt_composite] at h
  have heq : (((d.totient : ℝ) * residueOneMangoldt d N - mangoldtSum N : ℝ) : ℂ) =
      (∑ χ ∈ nonprincipalCharacters d, twistedArithmeticSum χ vonMangoldt N) -
        (nonunitMangoldt d N : ℂ) := by
    have hs : nonprincipalCharacters d = (univ : Finset (DirichletCharacter ℂ d)).erase 1 := by
      ext χ
      simp only [nonprincipalCharacters, mem_erase, mem_univ, and_true]
    rw [hs]
    push_cast at h ⊢
    linear_combination -h
  have hb : |(d.totient : ℝ) * residueOneMangoldt d N - mangoldtSum N| ≤
      (∑ χ ∈ nonprincipalCharacters d, ‖twistedArithmeticSum χ vonMangoldt N‖) + nonunitMangoldt d N := by
    calc
      _ = ‖(((d.totient : ℝ) * residueOneMangoldt d N - mangoldtSum N : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := by
        rw [heq]
        apply (norm_sub_le _ _).trans
        apply _root_.add_le_add (norm_sum_le _ _)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (nonunitMangoldt_nonneg d N)]
  apply (le_div_iff₀ hφ).mpr
  calc
    _ = |(residueOneMangoldt d N - mangoldtSum N / d.totient) * (d.totient : ℝ)| := by
      rw [abs_mul, abs_of_pos hφ]
    _ = |(d.totient : ℝ) * residueOneMangoldt d N - mangoldtSum N| := by
      congr 1
      field_simp
    _ ≤ _ := hb

noncomputable def compositeProgressionError (d N : ℕ) : ℝ :=
  (primitiveConductorMangoldtMajorant d N + ((d : ℝ) + 1) * characterLiftError d N) / d.totient

/-- A finite discrepancy bound valid for every positive composite or prime
modulus. The primitive conductor sums remain explicit. -/
theorem composite_progression_discrepancy (d N : ℕ) (hd : 0 < d) :
    |residueOneMangoldt d N - mangoldtSum N / d.totient| ≤ compositeProgressionError d N := by
  letI : NeZero d := ⟨hd.ne'⟩
  have hφ : (0 : ℝ) ≤ d.totient := Nat.cast_nonneg _
  apply (composite_progression_discrepancy_all_characters d N).trans
  calc
    _ ≤ ((primitiveConductorMangoldtMajorant d N + (d : ℝ) * characterLiftError d N) +
        characterLiftError d N) / d.totient :=
      div_le_div_of_nonneg_right (add_le_add
        (nonprincipal_mangoldt_sum_le_conductors d N hd.ne')
        (nonunitMangoldt_le_liftError d N hd.ne')) hφ
    _ = compositeProgressionError d N := by unfold compositeProgressionError; ring

/-- Summing the composite-modulus bound gives a total lower estimate with
an explicit, still-to-be-estimated primitive-conductor remainder. -/
theorem composite_progression_total_lower (D : Finset ℕ) (hD : ∀ d ∈ D, 0 < d) (N : ℕ) :
    mangoldtSum N * (∑ d ∈ D, (d.totient : ℝ)⁻¹) -
      (∑ d ∈ D, compositeProgressionError d N) ≤ ∑ d ∈ D, residueOneMangoldt d N := by
  have hlocal (d : ℕ) (hd : d ∈ D) :
      mangoldtSum N / d.totient - residueOneMangoldt d N ≤ compositeProgressionError d N := by
    have hneg : mangoldtSum N / d.totient - residueOneMangoldt d N ≤
        |residueOneMangoldt d N - mangoldtSum N / d.totient| := by
      simpa only [neg_sub] using
        neg_le_abs (residueOneMangoldt d N - mangoldtSum N / d.totient)
    exact hneg.trans (composite_progression_discrepancy d N (hD d hd))
  have h := Finset.sum_le_sum hlocal
  rw [Finset.sum_sub_distrib] at h
  simp only [div_eq_mul_inv, ← Finset.mul_sum] at h
  linarith only [h]

end Erdos821.AnalyticSieve
