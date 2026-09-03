import Submission.StationaryOddPrimeEnergy

/-! Fixed relative-width prime bands for the common-scale entropy transfer.
Their count has the usual PNT scale; no short-interval PNT is used. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex FiniteInformation AbelPrimes BlockPrimes
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

noncomputable def linearPrimeEndpoint (a : ℝ) (N : ℕ) : ℕ := ⌊a*(N : ℝ)⌋₊

lemma linearPrimeEndpoint_ratio (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun N : ℕ => (linearPrimeEndpoint a N : ℝ)/N) atTop (𝓝 a) :=
  (tendsto_nat_floor_mul_div_atTop ha).comp tendsto_natCast_atTop_atTop

lemma linearPrimeEndpoint_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (linearPrimeEndpoint a) atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop ha)

lemma linear_endpoint_log_ratio (U : ℕ → ℕ) (hU : Tendsto U atTop atTop)
    (r : ℝ) (hr : 0 < r) (h : Tendsto (fun N : ℕ => (U N : ℝ)/N) atTop (𝓝 r)) :
    Tendsto (fun N : ℕ => Real.log (U N : ℝ)/Real.log N) atTop (𝓝 1) := by
  have hlog := h.log hr.ne'
  have ht := hlog.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have ht' := ht.add_const 1
  simp only [zero_add] at ht'
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ),hU.eventually_ge_atTop 1] with N hN hUN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hu : (U N : ℝ) ≠ 0 := by exact_mod_cast (show U N ≠ 0 by omega)
  have hl : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  simp only [Function.comp_def]
  rw [Real.log_div hu hn]
  field_simp
  ring

lemma prime_count_at_linear_endpoint (U : ℕ → ℕ) (hU : Tendsto U atTop atTop)
    (r : ℝ) (hr : 0 < r) (h : Tendsto (fun N : ℕ => (U N : ℝ)/N) atTop (𝓝 r)) :
    Tendsto (fun N : ℕ => ((initialPrimes (U N)).card : ℝ)*Real.log N/N) atTop (𝓝 r) := by
  have ht := ((prime_number_theorem_initial.comp hU).div
    (linear_endpoint_log_ratio U hU r hr h) one_ne_zero).mul h
  simp only [one_div,inv_one,one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ),hU.eventually_ge_atTop 2] with N hN hUN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hu : (U N : ℝ) ≠ 0 := by exact_mod_cast (show U N ≠ 0 by omega)
  have hln : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have hlu : Real.log (U N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hUN)).ne'
  simp only [Function.comp_def,Pi.mul_apply,Pi.div_apply]
  field_simp

noncomputable def narrowPrimeBand (a b : ℝ) (N : ℕ) : Finset ℕ :=
  initialPrimes (linearPrimeEndpoint b N) \ initialPrimes (linearPrimeEndpoint a N)

lemma initialPrimes_mono {M N : ℕ} (h : M ≤ N) : initialPrimes M ⊆ initialPrimes N := by
  intro p hp
  obtain ⟨hp,hprime⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hp).1,(mem_Icc.mp hp).2.trans h⟩,hprime⟩

lemma linearPrimeEndpoint_mono {a b : ℝ} (hab : a ≤ b) (N : ℕ) :
    linearPrimeEndpoint a N ≤ linearPrimeEndpoint b N :=
  Nat.floor_mono (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg N))

lemma narrowPrimeBand_card_scaled_limit (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun N : ℕ => ((narrowPrimeBand a b N).card : ℝ)*Real.log N/N)
      atTop (𝓝 (b-a)) := by
  have hu := prime_count_at_linear_endpoint (linearPrimeEndpoint b) (linearPrimeEndpoint_tendsto b (ha.trans hab))
    b (ha.trans hab) (linearPrimeEndpoint_ratio b (ha.trans hab).le)
  have hl := prime_count_at_linear_endpoint (linearPrimeEndpoint a) (linearPrimeEndpoint_tendsto a ha)
    a ha (linearPrimeEndpoint_ratio a ha.le)
  have ht := hu.sub hl
  apply ht.congr'
  apply Eventually.of_forall
  intro N
  have hs := initialPrimes_mono (linearPrimeEndpoint_mono hab.le N)
  simp only [narrowPrimeBand,card_sdiff_of_subset hs,Nat.cast_sub (card_le_card hs)]
  ring

lemma narrowPrimeBand_eventual_count_lower (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∀ᶠ N : ℕ in atTop, ((b-a)/2)*N/Real.log N ≤ (narrowPrimeBand a b N).card := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    (narrowPrimeBand_card_scaled_limit a b ha hab).eventually_const_lt
      (by linarith : (b-a)/2 < b-a)] with N hN ht
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  apply (div_le_iff₀ hlog).mpr
  have hh := (lt_div_iff₀ hNr).mp ht
  linarith

lemma narrowPrimeBand_subset_halfBlock (a b : ℝ) (hb : b ≤ 1/2) (N : ℕ) :
    narrowPrimeBand a b N ⊆ halfBlockPrimes N := by
  intro p hp
  obtain ⟨hp,_⟩ := mem_sdiff.mp hp
  obtain ⟨hp,hprime⟩ := mem_filter.mp hp
  refine mem_halfBlockPrimes.mpr ⟨hprime,?_⟩
  have hpU := (mem_Icc.mp hp).2
  by_cases hb0 : 0 ≤ b
  · have hh : (p : ℝ) ≤ b*N := (by exact_mod_cast hpU : (p : ℝ) ≤ linearPrimeEndpoint b N).trans
      (Nat.floor_le (mul_nonneg hb0 (Nat.cast_nonneg N)))
    have hmul := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg (α := ℝ) N)
    have h : (2 : ℝ)*p ≤ N := by linarith
    exact_mod_cast h
  · have hz : linearPrimeEndpoint b N = 0 := Nat.floor_eq_zero.mpr (by
      have hh : b*(N : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg N)
      linarith)
    have := hprime.two_le
    omega

/-- Every prime in the band is close to the upper endpoint. The real bound
avoids discarding the floor on the lower endpoint. -/
lemma narrowPrimeBand_member_bounds (a b : ℝ) (N p : ℕ) (hp : p ∈ narrowPrimeBand a b N) :
    a*N < (p : ℝ) ∧ p ≤ linearPrimeEndpoint b N := by
  obtain ⟨hu,hl⟩ := mem_sdiff.mp hp
  obtain ⟨hpu,hprime⟩ := mem_filter.mp hu
  have hlo : linearPrimeEndpoint a N < p := by
    by_contra h
    exact hl (mem_filter.mpr ⟨mem_Icc.mpr ⟨hprime.pos,by omega⟩,hprime⟩)
  refine ⟨?_,(mem_Icc.mp hpu).2⟩
  by_cases haN : 0 ≤ a*(N : ℝ)
  · exact (Nat.floor_lt haN).mp hlo
  · exact (lt_of_not_ge haN).trans_le (Nat.cast_nonneg p)

#print axioms narrowPrimeBand_card_scaled_limit
#print axioms narrowPrimeBand_eventual_count_lower
end Erdos371.DilationSpectrum
