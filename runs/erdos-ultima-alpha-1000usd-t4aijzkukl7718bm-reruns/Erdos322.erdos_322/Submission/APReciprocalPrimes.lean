import FormalConjecturesUtil

/-! Reciprocal-prime divergence in reduced residue classes, obtained from the
von Mangoldt pole by dominated convergence. -/
namespace Erdos322Research.APReciprocalPrimes
noncomputable section
open Filter LSeries ArithmeticFunction.vonMangoldt
open scoped Topology Classical
set_option Elab.async false
set_option maxHeartbeats 0

lemma normalized_log_bound {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    t * (Real.log x / x ^ (1+t)) ≤ 1/x := by
  have h := Real.log_le_rpow_div hx.le ht
  have hpow := Real.rpow_pos_of_pos hx t
  rw [Real.rpow_add hx, Real.rpow_one]
  apply (le_div_iff₀ hx).mpr
  calc
    t * (Real.log x / (x * x ^ t)) * x = t * Real.log x / x^t := by field_simp
    _ ≤ 1 := (div_le_one hpow).mpr (by
      simpa [mul_comm] using (le_div_iff₀ ht).mp h)

/-- Prime reciprocals diverge in every reduced residue class. -/
theorem not_summable_prime_reciprocals {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    ¬ Summable (fun n : ℕ ↦ if n.Prime ∧ (n : ZMod q)=a then (1 : ℝ)/n else 0) := by
  intro hs
  let c : ℕ → ℂ := fun n ↦ residueClass a n
  let b : ℕ → ℝ := fun n ↦
    (if n.Prime ∧ (n : ZMod q)=a then (1 : ℝ)/n else 0) +
      (if n.Prime then 0 else residueClass a n)/n
  have hb : Summable b := hs.add (summable_residueClass_non_primes_div a)
  let f : ℝ → ℕ → ℂ := fun s n ↦ ((s : ℂ)-1)*LSeries.term c s n
  have hreal : Tendsto (fun s : ℝ ↦ s) (𝓝[>] (1 : ℝ)) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hcplx : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
    simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hlim (n : ℕ) : Tendsto (fun s ↦ f s n) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa [f] using (hcplx.sub (tendsto_const_nhds (x := (1 : ℂ)))).mul
      ((LSeries.hasDerivAt_term c n 1).continuousAt.tendsto.comp hcplx)
  have hbound : ∀ᶠ s in 𝓝[>] (1 : ℝ), ∀ n, ‖f s n‖ ≤ b n := by
    filter_upwards [self_mem_nhdsWithin, hreal.eventually (gt_mem_nhds (by norm_num : (1 : ℝ)<2))] with s hs1 hs2
    have hs1 : 1 < s := hs1
    intro n
    by_cases hn : n=0
    · subst n
      simp [f,b]
    have hn0 : (0 : ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn1 : (1 : ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hc : ‖c n‖ = residueClass a n := by
      simp only [c,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (residueClass_nonneg a n)]
    have hnrm : ‖f s n‖=(s-1)*(residueClass a n/(n : ℝ)^s) := by
      simp only [f,norm_mul,LSeries.norm_term_eq,hn,if_false,Complex.ofReal_re,hc]
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (sub_pos.mpr hs1)]
    rw [hnrm]
    by_cases hp : n.Prime
    · by_cases hna : (n : ZMod q)=a
      · simp only [b,hp,hna,and_self,if_true,zero_div,add_zero]
        simp only [residueClass, Set.indicator_apply, Set.mem_setOf_eq, hna, if_true,
          ArithmeticFunction.vonMangoldt_apply_prime hp]
        simpa only [show (1 : ℝ)+(s-1)=s by ring] using
          normalized_log_bound hn0 (sub_pos.mpr hs1)
      · simp [b,hp,hna,residueClass]
    · simp only [b,hp,false_and,if_false,zero_add]
      have he : (n : ℝ) ≤ (n : ℝ)^s := by
        simpa using Real.rpow_le_rpow_of_exponent_le hn1 hs1.le
      have hle : residueClass a n/(n : ℝ)^s ≤ residueClass a n/n :=
        div_le_div_of_nonneg_left (residueClass_nonneg a n) hn0 he
      calc
        (s-1)*(residueClass a n/(n : ℝ)^s) ≤ 1*(residueClass a n/(n : ℝ)^s) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity [residueClass_nonneg a n])
        _ ≤ _ := by simpa using hle
  have hz : Tendsto (fun s : ℝ ↦ ((s : ℂ)-1)*LSeries c s)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence hb hlim hbound
    simpa only [f,tsum_mul_left,tsum_zero,LSeries] using h
  have haux : Tendsto (fun s : ℝ ↦ LFunctionResidueClassAux a s)
      (𝓝[>] (1 : ℝ)) (𝓝 (LFunctionResidueClassAux a 1)) := by
    apply (continuousOn_LFunctionResidueClassAux a 1 (by simp)).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hcplx,?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact show 1 ≤ (s : ℂ).re from le_of_lt hs
  have hpole : Tendsto (fun s : ℝ ↦ ((s : ℂ)-1)*LSeries c s)
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℂ)⁻¹)) := by
    have h := ((hcplx.sub (tendsto_const_nhds (x := (1 : ℂ)))).mul haux).add_const ((q.totient : ℂ)⁻¹)
    simp only [sub_self,zero_mul,zero_add] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs : 1<s := hs
    have hne : (s : ℂ)-1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.sub_re,Complex.ofReal_re,Complex.one_re,Complex.zero_re] at this
      linarith
    rw [eqOn_LFunctionResidueClassAux ha (show 1 < (s : ℂ).re from hs)]
    change ((s : ℂ)-1)*(LSeries c s-(q.totient : ℂ)⁻¹/((s : ℂ)-1))+
      (q.totient : ℂ)⁻¹ = _
    field_simp
    ring
  have heq := tendsto_nhds_unique hz hpole
  have ht : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  exact (inv_ne_zero ht) heq.symm

end
end Erdos322Research.APReciprocalPrimes
