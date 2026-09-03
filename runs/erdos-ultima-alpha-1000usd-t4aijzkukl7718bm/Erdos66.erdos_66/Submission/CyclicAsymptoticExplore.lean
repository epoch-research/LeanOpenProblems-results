import Submission.CyclicMeanTuningExplore

/-! Finite cyclic analogues at every sufficiently large modulus, for any
positive divergent sublinear target mean. These are independently selected
finite sets, not prefixes of one subset of the natural numbers. -/
namespace Erdos66CyclicAsymptotic
open Filter Erdos66CyclicMeanTuning
open scoped Classical Topology
set_option linter.style.existsImplication false

noncomputable def cyclicCount (N : ℕ) (B : Finset (ZMod N)) (z : ZMod N) : ℝ :=
  ((B.filter (fun a ↦ z-a∈B)).card : ℝ)

/-- Every divergent sublinear mean is uniformly realizable at each large
finite cyclic modulus, at any prescribed fixed relative precision. -/
theorem eventually_prescribed_mean (f : ℕ → ℝ)
    (hf : Tendsto f atTop atTop)
    (hsub : Tendsto (fun N ↦ f N/(N : ℝ)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ B : Finset (ZMod N), ∀ z : ZMod N,
      |cyclicCount N B z-f N| ≤ ε*f N := by
  obtain ⟨a,b,ha,hb,h⟩ := prescribed_mean ε hε
  have h₁ : ∀ᶠ N in atTop, a ≤ f N := (tendsto_atTop.1 hf) a
  have h₂ : ∀ᶠ N in atTop, f N/(N : ℝ) ≤ 1/b :=
    hsub.eventually_le_const (by positivity)
  filter_upwards [h₁,h₂,eventually_ge_atTop 1] with N hN₁ hN₂ hN₃
  have hN : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hbN : b*f N ≤ N := by
    have hh := (div_le_iff₀ hNr).mp hN₂
    have hh' := mul_le_mul_of_nonneg_left hh hb.le
    field_simp at hh'
    nlinarith
  exact h N hN (f N) hN₁ hbN

/-- A minimax choice avoids any compatibility claims: it merely picks a
best finite set separately at each modulus. -/
lemma exists_optimal_finite_set (N : ℕ) [NeZero N] (μ : ℝ) :
    ∃ B : Finset (ZMod N), ∀ C : Finset (ZMod N), ∀ t : ℝ,
      (∀ z : ZMod N, |cyclicCount N C z-μ| ≤ t) →
      ∀ z : ZMod N, |cyclicCount N B z-μ| ≤ t := by
  let err : Finset (ZMod N) → ℝ := fun C ↦
    Finset.univ.sup' Finset.univ_nonempty (fun z ↦ |cyclicCount N C z-μ|)
  obtain ⟨B,hB,hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Finset (ZMod N))) err Finset.univ_nonempty
  refine ⟨B,fun C t hC z ↦ ?_⟩
  have hc : err C ≤ t := Finset.sup'_le _ _ (fun z hz ↦ hC z)
  have hb : |cyclicCount N B z-μ| ≤ err B := Finset.le_sup' (fun z ↦ |cyclicCount N B z-μ|) (Finset.mem_univ z)
  exact hb.trans ((hmin C (Finset.mem_univ C)).trans hc)

/-- One can select a sequence of independently chosen finite cyclic sets
whose relative error tends to zero uniformly over all cyclic targets. -/
theorem exists_uniformly_flat_sequence (f : ℕ → ℝ)
    (hf : Tendsto f atTop atTop)
    (hsub : Tendsto (fun N ↦ f N/(N : ℝ)) atTop (𝓝 0)) :
    ∃ B : (N : ℕ) → Finset (ZMod N), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ z : ZMod N,
        |cyclicCount N (B N) z/f N-1| ≤ ε := by
  have hopt : ∀ N : ℕ, ∃ B : Finset (ZMod N), 0 < N →
      ∀ C : Finset (ZMod N), ∀ t : ℝ,
        (∀ z : ZMod N, |cyclicCount N C z-f N| ≤ t) →
        ∀ z : ZMod N, |cyclicCount N B z-f N| ≤ t := by
    intro N
    by_cases hN : 0 < N
    · letI : NeZero N := ⟨by omega⟩
      obtain ⟨B,hB⟩ := exists_optimal_finite_set N (f N)
      exact ⟨B,fun _ ↦ hB⟩
    · exact ⟨∅,fun hh ↦ (hN hh).elim⟩
  choose B hB using hopt
  refine ⟨B,fun ε hε ↦ ?_⟩
  have hfpos : ∀ᶠ N in atTop, 1 ≤ f N := (tendsto_atTop.1 hf) 1
  filter_upwards [eventually_prescribed_mean f hf hsub ε hε,hfpos,eventually_ge_atTop 1]
    with N hN hfN hNpos
  obtain ⟨C,hC⟩ := hN
  have hh := hB N (by omega) C (ε*f N) hC
  have hfNpos : 0 < f N := by linarith
  intro z
  have he : cyclicCount N (B N) z/f N-1=(cyclicCount N (B N) z-f N)/f N := by
    field_simp
  rw [he,abs_div,abs_of_pos hfNpos]
  exact (div_le_iff₀ hfNpos).mpr (hh z)

/-- The uniform finite conclusion implies a limit along every sequence of
target residues, still with a separate finite set at each modulus. -/
theorem exists_flat_sequence_limits (f : ℕ → ℝ)
    (hf : Tendsto f atTop atTop)
    (hsub : Tendsto (fun N ↦ f N/(N : ℝ)) atTop (𝓝 0)) :
    ∃ B : (N : ℕ) → Finset (ZMod N), ∀ z : (N : ℕ) → ZMod N,
      Tendsto (fun N ↦ cyclicCount N (B N) (z N)/f N) atTop (𝓝 1) := by
  obtain ⟨B,hB⟩ := exists_uniformly_flat_sequence f hf hsub
  refine ⟨B,fun z ↦ Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hB (ε/2) (by positivity))
  refine ⟨N,fun n hn ↦ ?_⟩
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (hN n hn (z n)) (by linarith)

/-- In particular the logarithmic finite cyclic analogue holds, with any
positive coefficient c, at every modulus rather than just selected primes. -/
theorem logarithmic_cyclic_analogue (c : ℝ) (hc : 0 < c) :
    ∃ B : (N : ℕ) → Finset (ZMod N), ∀ z : (N : ℕ) → ZMod N,
      Tendsto (fun N ↦ cyclicCount N (B N) (z N)/Real.log N) atTop (𝓝 c) := by
  have hf : Tendsto (fun N : ℕ ↦ c*Real.log N) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  have hsub : Tendsto (fun N : ℕ ↦ (c*Real.log N)/(N : ℝ)) atTop (𝓝 0) := by
    have hh := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul c
    simpa only [Function.comp_apply,id_eq,mul_zero,mul_div_assoc] using hh
  obtain ⟨B,hB⟩ := exists_flat_sequence_limits (fun N ↦ c*Real.log N) hf hsub
  refine ⟨B,fun z ↦ ?_⟩
  have hh := (hB z).const_mul c
  convert hh using 1
  · funext N
    field_simp
  · ring

end Erdos66CyclicAsymptotic
