import Submission.LogPrimeBlocks

/-!
A uniform pole approximation for the prime logarithmic Dirichlet series on compact
vertical frequency ranges. This is a preparatory step for prime-ratio density, not
an assertion of the original fixed-slope prime-pair conjecture.
-/
namespace Erdos972PrimeDirichletPole

open ArithmeticFunction Finset

noncomputable def primeCoeff (n : ℕ) : ℂ :=
  if n.Prime then (Real.log n : ℂ) else 0

noncomputable def powerCoeff (n : ℕ) : ℂ :=
  if n.Prime then 0 else (Λ n : ℂ)

noncomputable def powerMajorant (n : ℕ) : ℝ :=
  (if n.Prime then 0 else Λ n) / n

lemma residueClass_one (n : ℕ) : vonMangoldt.residueClass (1 : ZMod 1) n = Λ n := by
  simp [vonMangoldt.residueClass, Subsingleton.elim (n : ZMod 1) 1]

lemma summable_powerMajorant : Summable powerMajorant := by
  simpa only [residueClass_one] using
    vonMangoldt.summable_residueClass_non_primes_div (1 : ZMod 1)

lemma powerMajorant_nonneg (n : ℕ) : 0 ≤ powerMajorant n := by
  unfold powerMajorant
  positivity [vonMangoldt_nonneg (n := n)]

lemma norm_power_term_one (n : ℕ) : ‖LSeries.term powerCoeff 1 n‖ = powerMajorant n := by
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst n
    simp [powerMajorant]
  · simp only [if_neg hn, Complex.one_re, Real.rpow_one]
    unfold powerCoeff powerMajorant
    split_ifs <;> simp [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (vonMangoldt_nonneg (n := n))]

lemma norm_power_term_le {s : ℂ} (hs : 1 ≤ s.re) (n : ℕ) :
    ‖LSeries.term powerCoeff s n‖ ≤ powerMajorant n := by
  rw [← norm_power_term_one]
  exact LSeries.norm_term_le_of_re_le_re _ hs n

lemma summable_power_term {s : ℂ} (hs : 1 ≤ s.re) : LSeriesSummable powerCoeff s :=
  summable_powerMajorant.of_norm_bounded (norm_power_term_le hs)

noncomputable def powerMass : ℝ := ∑' n, powerMajorant n

lemma powerMass_nonneg : 0 ≤ powerMass := tsum_nonneg powerMajorant_nonneg

lemma norm_power_LSeries_le {s : ℂ} (hs : 1 ≤ s.re) :
    ‖LSeries powerCoeff s‖ ≤ powerMass := by
  have hsn : Summable (fun n => ‖LSeries.term powerCoeff s n‖) :=
    (summable_power_term hs).norm
  exact (norm_tsum_le_tsum_norm hsn).trans
    (Summable.tsum_le_tsum (norm_power_term_le hs) hsn summable_powerMajorant)

lemma primeCoeff_eq_sub : primeCoeff = (fun n => (Λ n : ℂ)) - powerCoeff := by
  funext n
  simp only [Pi.sub_apply, primeCoeff, powerCoeff]
  by_cases hn : n.Prime
  · simp [hn, vonMangoldt_apply_prime hn]
  · simp [hn]

lemma summable_prime_term {s : ℂ} (hs : 1 < s.re) : LSeriesSummable primeCoeff s := by
  rw [primeCoeff_eq_sub]
  exact (LSeriesSummable_vonMangoldt hs).sub (summable_power_term hs.le)

lemma prime_LSeries_eq_sub {s : ℂ} (hs : 1 < s.re) :
    LSeries primeCoeff s = LSeries (fun n => (Λ n : ℂ)) s - LSeries powerCoeff s := by
  rw [primeCoeff_eq_sub, LSeries_sub (LSeriesSummable_vonMangoldt hs) (summable_power_term hs.le)]

noncomputable def mangoldtAux : ℂ → ℂ :=
  vonMangoldt.LFunctionResidueClassAux (1 : ZMod 1)

lemma continuousOn_mangoldtAux : ContinuousOn mangoldtAux {s | 1 ≤ s.re} :=
  vonMangoldt.continuousOn_LFunctionResidueClassAux _

lemma mangoldtAux_eq {s : ℂ} (hs : 1 < s.re) :
    mangoldtAux s = LSeries (fun n => (Λ n : ℂ)) s - 1 / (s - 1) := by
  have h := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) (a := 1) isUnit_one hs
  simpa only [mangoldtAux, residueClass_one, Nat.totient_one, Nat.cast_one, inv_one] using h

lemma mangoldtAux_bounded_rectangle (T : ℝ) :
    ∃ C : ℝ, ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → |t| ≤ T →
      ‖mangoldtAux ((σ : ℂ) + Complex.I * t)‖ ≤ C := by
  let K : Set (ℝ × ℝ) := Set.Icc (1 : ℝ) 2 ×ˢ Set.Icc (-T) T
  let f : ℝ × ℝ → ℂ := fun z => (z.1 : ℂ) + Complex.I * z.2
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hc : ContinuousOn (fun z => ‖mangoldtAux (f z)‖) K := by
    apply continuousOn_mangoldtAux.norm.comp hf.continuousOn
    intro z hz
    simpa [f] using hz.1.1
  obtain ⟨C, hC⟩ := bddAbove_def.mp ((isCompact_Icc.prod isCompact_Icc).bddAbove_image hc)
  refine ⟨C, ?_⟩
  intro σ t hσ1 hσ2 ht
  apply hC
  exact ⟨(σ, t), ⟨⟨hσ1, hσ2⟩, abs_le.mp ht⟩, rfl⟩

noncomputable def primeDirichlet (ε t : ℝ) : ℂ :=
  LSeries primeCoeff (((1 + ε : ℝ) : ℂ) + Complex.I * t)

/-- The prime-only series has the same simple pole as `-ζ'/ζ`, with a uniformly
bounded remainder on every fixed vertical frequency range. -/
theorem uniform_prime_pole_bound (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε t : ℝ, 0 < ε → ε ≤ 1 → |t| ≤ T →
      ‖primeDirichlet ε t - ((ε : ℂ) + Complex.I * t)⁻¹‖ ≤ C := by
  obtain ⟨M, hM⟩ := mangoldtAux_bounded_rectangle T
  refine ⟨max M 0 + powerMass + 1, by have := powerMass_nonneg; positivity, ?_⟩
  intro ε t hε hε1 ht
  let s : ℂ := ((1 + ε : ℝ) : ℂ) + Complex.I * t
  have hs : 1 < s.re := by
    simpa [s] using (lt_add_of_pos_right (1 : ℝ) hε)
  have he : s - 1 = (ε : ℂ) + Complex.I * t := by dsimp [s]; push_cast; ring
  have hrewrite : primeDirichlet ε t - ((ε : ℂ) + Complex.I * t)⁻¹ =
      mangoldtAux s - LSeries powerCoeff s := by
    change LSeries primeCoeff s - _ = _
    rw [prime_LSeries_eq_sub hs, mangoldtAux_eq hs, he, one_div]
    ring
  rw [hrewrite]
  have hb := hM (1 + ε) t (by linarith) (by linarith) ht
  change ‖mangoldtAux s‖ ≤ M at hb
  calc
    _ ≤ ‖mangoldtAux s‖ + ‖LSeries powerCoeff s‖ := norm_sub_le _ _
    _ ≤ M + powerMass := add_le_add hb (norm_power_LSeries_le hs.le)
    _ ≤ max M 0 + powerMass + 1 := by linarith [le_max_left M 0]

open Erdos972LogPrimeBlocks

noncomputable def truncPrimes (L : ℕ) : Finset ℕ := by
  classical
  exact (Ioc 0 ⌊Real.exp (L : ℝ)⌋₊).filter Nat.Prime

noncomputable def primeTrunc (ε t : ℝ) (L : ℕ) : ℂ :=
  ∑ p ∈ truncPrimes L,
    LSeries.term primeCoeff (((1 + ε : ℝ) : ℂ) + Complex.I * t) p

lemma norm_prime_term (ε t : ℝ) (n : ℕ) :
    ‖LSeries.term primeCoeff (((1 + ε : ℝ) : ℂ) + Complex.I * t) n‖ =
      if n.Prime then primeWeight ε n else 0 := by
  by_cases hp : n.Prime
  · rw [if_pos hp, primeWeight_eq_div_rpow ε hp.pos, LSeries.norm_term_eq]
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
    simp only [if_neg hp.ne_zero, primeCoeff, if_pos hp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlog]
    simp
  · rw [if_neg hp, LSeries.norm_term_eq]
    simp [primeCoeff, hp]

lemma log_le_of_mem_truncPrimes {L p : ℕ} (hp : p ∈ truncPrimes L) :
    p.Prime ∧ Real.log p ≤ L := by
  obtain ⟨hpL, hpp⟩ := mem_filter.mp hp
  refine ⟨hpp, ?_⟩
  have hple := Nat.le_floor_iff (Real.exp_pos (L : ℝ)).le |>.mp (mem_Ioc.mp hpL).2
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hpp.pos) hple
  simpa only [Real.log_exp] using hlog

lemma log_le_of_not_mem_truncPrimes {L p : ℕ} (hp : p.Prime)
    (hn : p ∉ truncPrimes L) : (L : ℝ) ≤ Real.log p := by
  have hPp : ⌊Real.exp (L : ℝ)⌋₊ < p := by
    by_contra h
    exact hn (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp.pos, Nat.le_of_not_gt h⟩, hp⟩)
  have hplarge := (Nat.floor_lt (Real.exp_pos (L : ℝ)).le).mp hPp
  have hlog := Real.log_le_log (Real.exp_pos (L : ℝ)) hplarge.le
  simpa only [Real.log_exp] using hlog

/-- Uniform truncation error, independent of the imaginary part of the series
parameter. The logarithmic cutoff makes the error exponentially small. -/
theorem norm_primeDirichlet_sub_primeTrunc_le {ε : ℝ} (hε : 0 < ε)
    (t : ℝ) (L : ℕ) :
    ‖primeDirichlet ε t - primeTrunc ε t L‖ ≤
      Real.exp 1 * Real.log 4 * Real.exp (-ε * L) / (1 - Real.exp (-ε)) := by
  classical
  let s : ℂ := ((1 + ε : ℝ) : ℂ) + Complex.I * t
  let f : ℕ → ℂ := LSeries.term primeCoeff s
  let g : ℕ → ℂ := (↑(truncPrimes L) : Set ℕ)ᶜ.indicator f
  have hs : 1 < s.re := by simpa [s] using (lt_add_of_pos_right (1 : ℝ) hε)
  have hf : Summable f := summable_prime_term hs
  have hg : Summable g := hf.indicator _
  have hgN (n : ℕ) : ‖g n‖ =
      if n ∉ truncPrimes L ∧ n.Prime then primeWeight ε n else 0 := by
    by_cases hn : n ∈ truncPrimes L
    · simp [g, hn]
    · have hm : n ∈ (↑(truncPrimes L) : Set ℕ)ᶜ := hn
      simp only [g, Set.indicator_of_mem hm, f, s, norm_prime_term]
      simp [hn]
  have htail : (∑' n, ‖g n‖) ≤
      Real.exp 1 * Real.log 4 * Real.exp (-ε * L) / (1 - Real.exp (-ε)) := by
    apply hg.norm.tsum_le_of_sum_le
    intro S
    simp_rw [hgN]
    rw [← sum_filter]
    apply sum_primeWeight_tail_le hε
    intro p hp
    obtain ⟨_, hn, hpp⟩ := mem_filter.mp hp
    exact ⟨hpp, log_le_of_not_mem_truncPrimes hpp hn⟩
  have he := hf.sum_add_tsum_subtype_compl (truncPrimes L)
  have ht : (∑' n : {n // n ∉ truncPrimes L}, f n) = ∑' n, g n := by
    exact _root_.tsum_subtype {n | n ∉ truncPrimes L} f
  rw [ht] at he
  have hdiff : primeDirichlet ε t - primeTrunc ε t L = ∑' n, g n := by
    change (∑' n, f n) - (∑ p ∈ truncPrimes L, f p) = _
    change (∑ p ∈ truncPrimes L, f p) + (∑' n, g n) = (∑' n, f n) at he
    rw [← he]
    ring
  rw [hdiff]
  exact (norm_tsum_le_tsum_norm hg.norm).trans htail

/-- Combining the pole and tail estimates gives a finite prime sum with a
uniform, explicit approximation to the pole. -/
theorem uniform_primeTrunc_pole_bound (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε t : ℝ, 0 < ε → ε ≤ 1 → |t| ≤ T → ∀ L : ℕ,
      ‖primeTrunc ε t L - ((ε : ℂ) + Complex.I * t)⁻¹‖ ≤ C +
        Real.exp 1 * Real.log 4 * Real.exp (-ε * L) / (1 - Real.exp (-ε)) := by
  obtain ⟨C, hC, hb⟩ := uniform_prime_pole_bound T
  refine ⟨C, hC, ?_⟩
  intro ε t hε hε1 ht L
  calc
    _ ≤ ‖primeTrunc ε t L - primeDirichlet ε t‖ +
        ‖primeDirichlet ε t - ((ε : ℂ) + Complex.I * t)⁻¹‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (Real.exp 1 * Real.log 4 * Real.exp (-ε * L) / (1 - Real.exp (-ε))) + C := by
      apply add_le_add _ (hb ε t hε hε1 ht)
      rw [norm_sub_rev]
      exact norm_primeDirichlet_sub_primeTrunc_le hε t L
    _ = _ := add_comm _ _

#print axioms norm_primeDirichlet_sub_primeTrunc_le
#print axioms uniform_primeTrunc_pole_bound
#print axioms uniform_prime_pole_bound

end Erdos972PrimeDirichletPole
