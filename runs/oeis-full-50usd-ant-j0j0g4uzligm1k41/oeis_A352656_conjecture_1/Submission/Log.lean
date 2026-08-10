import FormalConjectures.Util.ProblemImports
open scoped Classical
open Filter Topology Finset

variable {p : ℕ} [hp : Fact p.Prime]

lemma normp : ‖(p : ℚ_[p])‖ = (p:ℝ)⁻¹ := Padic.norm_p

lemma norm_choose_le (k : ℕ) (h0 : 0 < k) (hk : k < p) : ‖(p.choose k : ℚ_[p])‖ ≤ (p:ℝ)⁻¹ := by
  have hd : p ∣ p.choose k := Nat.Prime.dvd_choose_self hp.out (by omega) hk
  obtain ⟨m, hm⟩ := hd
  have : (p.choose k : ℚ_[p]) = (p : ℚ_[p]) * (m : ℚ_[p]) := by rw [hm]; push_cast; ring
  rw [this, norm_mul, normp]
  have hm1 : ‖(m : ℚ_[p])‖ ≤ 1 := by
    have := PadicInt.norm_le_one (m : ℤ_[p]); simpa using this
  nlinarith [norm_nonneg (m : ℚ_[p]), inv_nonneg.mpr (le_of_lt (by exact_mod_cast hp.out.pos : (0:ℝ) < p))]

lemma pinv_pos : (0:ℝ) < (p:ℝ)⁻¹ := by
  have : (0:ℝ) < p := by exact_mod_cast hp.out.pos
  positivity

lemma pow_step (a : ℚ_[p]) (ha : ‖a‖ ≤ (p:ℝ)⁻¹) : ‖(1 + a)^p - 1‖ ≤ (p:ℝ)⁻¹ * ‖a‖ := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.out.pos
  have hple1 : (p:ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ hp0]; exact_mod_cast hp.out.one_lt.le
  have ha1 : ‖a‖ ≤ 1 := le_trans ha hple1
  have hexp : (1 + a)^p - 1 = ∑ k ∈ Finset.range p, a^(k+1) * (p.choose (k+1) : ℚ_[p]) := by
    have := add_pow a (1:ℚ_[p]) p
    simp only [one_pow, mul_one] at this
    rw [add_comm a 1] at *
    rw [this, Finset.sum_range_succ']
    simp
  rw [hexp]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro k hk
  simp only [Finset.mem_range] at hk
  rw [norm_mul, norm_pow]
  rcases Nat.lt_or_ge (k+1) p with hlt | hge
  · have hc : ‖(p.choose (k+1) : ℚ_[p])‖ ≤ (p:ℝ)⁻¹ := norm_choose_le (k+1) (by omega) hlt
    have hak : ‖a‖^(k+1) ≤ ‖a‖ := by
      calc ‖a‖^(k+1) ≤ ‖a‖^1 := pow_le_pow_of_le_one (norm_nonneg a) ha1 (by omega)
        _ = ‖a‖ := pow_one _
    calc ‖a‖^(k+1) * ‖(p.choose (k+1):ℚ_[p])‖ ≤ ‖a‖ * (p:ℝ)⁻¹ := by
          apply mul_le_mul hak hc (norm_nonneg _) (norm_nonneg a)
      _ = (p:ℝ)⁻¹ * ‖a‖ := by ring
  · have hkp : k + 1 = p := by omega
    rw [hkp]
    have : (p.choose p : ℚ_[p]) = 1 := by simp
    rw [this, norm_one, mul_one]
    -- ‖a‖^p ≤ p⁻¹ * ‖a‖
    have : ‖a‖^p = ‖a‖^(p-1) * ‖a‖ := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg a)
    calc ‖a‖^(p-1) ≤ ((p:ℝ)⁻¹)^(p-1) := by
          apply pow_le_pow_left₀ (norm_nonneg a) ha
      _ ≤ ((p:ℝ)⁻¹)^1 := by
          apply pow_le_pow_of_le_one (by positivity) hple1 (by have := hp.out.two_le; omega)
      _ = (p:ℝ)⁻¹ := pow_one _

lemma pow_pn_bound (t : ℚ_[p]) (ht : ‖t - 1‖ ≤ (p:ℝ)⁻¹) (n : ℕ) :
    ‖t^(p^n) - 1‖ ≤ ((p:ℝ)⁻¹)^(n+1) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.out.pos
  have hple1 : (p:ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ hp0]; exact_mod_cast hp.out.one_lt.le
  induction n with
  | zero => simpa using ht
  | succ n ih =>
    have hs : ‖t^(p^n) - 1‖ ≤ (p:ℝ)⁻¹ := by
      refine le_trans ih ?_
      calc ((p:ℝ)⁻¹)^(n+1) ≤ ((p:ℝ)⁻¹)^1 :=
            pow_le_pow_of_le_one (by positivity) hple1 (by omega)
        _ = (p:ℝ)⁻¹ := pow_one _
    have hrw : t^(p^(n+1)) = (1 + (t^(p^n) - 1))^p := by
      rw [show (1 + (t^(p^n) - 1)) = t^(p^n) by ring, ← pow_mul, pow_succ]
    rw [hrw]
    refine le_trans (pow_step (t^(p^n) - 1) hs) ?_
    calc (p:ℝ)⁻¹ * ‖t^(p^n) - 1‖ ≤ (p:ℝ)⁻¹ * ((p:ℝ)⁻¹)^(n+1) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ = ((p:ℝ)⁻¹)^(n+2) := by ring

lemma pow_step2 (a : ℚ_[p]) (ha : ‖a‖ ≤ (p:ℝ)⁻¹) :
    ‖(1 + a)^p - 1 - (p:ℚ_[p]) * a‖ ≤ ‖a‖^2 := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.out.pos
  have hple1 : (p:ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ hp0]; exact_mod_cast hp.out.one_lt.le
  have ha1 : ‖a‖ ≤ 1 := le_trans ha hple1
  have hexp : (1 + a)^p - 1 = ∑ k ∈ Finset.range p, a^(k+1) * (p.choose (k+1) : ℚ_[p]) := by
    have := add_pow a (1:ℚ_[p]) p
    simp only [one_pow, mul_one] at this
    rw [add_comm a 1] at *
    rw [this, Finset.sum_range_succ']
    simp
  have hmem : (0:ℕ) ∈ Finset.range p := Finset.mem_range.mpr hp.out.pos
  have hexp2 : (1 + a)^p - 1 - (p:ℚ_[p]) * a
      = ∑ k ∈ (Finset.range p).erase 0, a^(k+1) * (p.choose (k+1) : ℚ_[p]) := by
    rw [hexp, ← Finset.add_sum_erase _ _ hmem]
    simp only [zero_add, pow_one, Nat.choose_one_right]
    ring
  rw [hexp2]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro k hk
  simp only [Finset.mem_erase, Finset.mem_range] at hk
  obtain ⟨hk0, hkp'⟩ := hk
  rw [norm_mul, norm_pow]
  have hak2 : ‖a‖^(k+1) ≤ ‖a‖^2 := pow_le_pow_of_le_one (norm_nonneg a) ha1 (by omega)
  have hc1 : ‖(p.choose (k+1) : ℚ_[p])‖ ≤ 1 := by
    have := PadicInt.norm_le_one ((p.choose (k+1) : ℕ) : ℤ_[p]); simpa using this
  calc ‖a‖^(k+1) * ‖(p.choose (k+1):ℚ_[p])‖ ≤ ‖a‖^2 * 1 :=
        mul_le_mul hak2 hc1 (norm_nonneg _) (by positivity)
    _ = ‖a‖^2 := by ring

lemma normp_pow (n : ℕ) : ‖(p:ℚ_[p])^n‖ = ((p:ℝ)⁻¹)^n := by
  rw [norm_pow, normp]

-- consecutive difference bound for the log-sequence
lemma cauchy_step (t : ℚ_[p]) (ht : ‖t - 1‖ ≤ (p:ℝ)⁻¹) (n : ℕ) :
    ‖(t^(p^(n+1)) - 1)/(p:ℚ_[p])^(n+1) - (t^(p^n) - 1)/(p:ℚ_[p])^n‖ ≤ ((p:ℝ)⁻¹)^(n+1) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.out.pos
  set a := t^(p^n) - 1 with ha_def
  have hta : t^(p^n) = 1 + a := by rw [ha_def]; ring
  have habound : ‖a‖ ≤ ((p:ℝ)⁻¹)^(n+1) := pow_pn_bound t ht n
  have hale : ‖a‖ ≤ (p:ℝ)⁻¹ := by
    refine le_trans habound ?_
    calc ((p:ℝ)⁻¹)^(n+1) ≤ ((p:ℝ)⁻¹)^1 :=
          pow_le_pow_of_le_one (by positivity) (by rw [inv_le_one₀ hp0]; exact_mod_cast hp.out.one_lt.le) (by omega)
      _ = (p:ℝ)⁻¹ := pow_one _
  have hpne : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have key : (t^(p^(n+1)) - 1)/(p:ℚ_[p])^(n+1) - (t^(p^n) - 1)/(p:ℚ_[p])^n
      = ((1+a)^p - 1 - (p:ℚ_[p])*a) / (p:ℚ_[p])^(n+1) := by
    have e1 : t^(p^(n+1)) = (1+a)^p := by
      rw [show p^(n+1) = p^n * p by rw [pow_succ], pow_mul, ← hta]
    rw [e1, ha_def]
    field_simp
    ring
  rw [key, norm_div, normp_pow]
  rw [div_le_iff₀ (by positivity)]
  calc ‖(1+a)^p - 1 - (p:ℚ_[p])*a‖ ≤ ‖a‖^2 := pow_step2 a hale
    _ ≤ (((p:ℝ)⁻¹)^(n+1))^2 := by
        apply pow_le_pow_left₀ (norm_nonneg a) habound
    _ = ((p:ℝ)⁻¹)^(n+1) * ((p:ℝ)⁻¹)^(n+1) := by ring

noncomputable def gseq (t : ℚ_[p]) (n : ℕ) : ℚ_[p] := (t^(p^n) - 1)/(p:ℚ_[p])^n

lemma gseq_cauchy (t : ℚ_[p]) (ht : ‖t - 1‖ ≤ (p:ℝ)⁻¹) : CauchySeq (gseq t) := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.out.pos
  have hr1 : (p:ℝ)⁻¹ < 1 := by rw [inv_lt_one₀ hp0]; exact_mod_cast hp.out.one_lt
  apply cauchySeq_of_le_geometric (p:ℝ)⁻¹ (p:ℝ)⁻¹ hr1
  intro n
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  have := cauchy_step t ht n
  calc ‖gseq t (n+1) - gseq t n‖ ≤ ((p:ℝ)⁻¹)^(n+1) := this
    _ = (p:ℝ)⁻¹ * ((p:ℝ)⁻¹)^n := by rw [pow_succ]; ring

noncomputable def logp (t : ℚ_[p]) : ℚ_[p] := limUnder Filter.atTop (gseq t)

lemma gseq_tendsto (t : ℚ_[p]) (ht : ‖t - 1‖ ≤ (p:ℝ)⁻¹) :
    Filter.Tendsto (gseq t) Filter.atTop (nhds (logp t)) :=
  (gseq_cauchy t ht).tendsto_limUnder

lemma norm_one_unit (t : ℚ_[p]) (ht : ‖t - 1‖ ≤ (p:ℝ)⁻¹) : ‖t‖ ≤ 1 := by
  have hple1 : (p:ℝ)⁻¹ ≤ 1 := by
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.out.pos
    rw [inv_le_one₀ hp0]; exact_mod_cast hp.out.one_lt.le
  calc ‖t‖ = ‖(t-1) + 1‖ := by ring_nf
    _ ≤ max ‖t-1‖ ‖(1:ℚ_[p])‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := by rw [norm_one]; apply max_le (le_trans ht hple1) le_rfl

lemma norm_mul_sub_one (s t : ℚ_[p]) (hs : ‖s - 1‖ ≤ (p:ℝ)⁻¹) (ht : ‖t - 1‖ ≤ (p:ℝ)⁻¹) :
    ‖s * t - 1‖ ≤ (p:ℝ)⁻¹ := by
  have : s * t - 1 = (s - 1) * t + (t - 1) := by ring
  rw [this]
  calc ‖(s-1)*t + (t-1)‖ ≤ max ‖(s-1)*t‖ ‖t-1‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ (p:ℝ)⁻¹ := by
        apply max_le _ ht
        rw [norm_mul]
        calc ‖s-1‖ * ‖t‖ ≤ (p:ℝ)⁻¹ * 1 := mul_le_mul hs (norm_one_unit t ht) (norm_nonneg _) (by positivity)
          _ = (p:ℝ)⁻¹ := by ring

lemma gseq_mul (s t : ℚ_[p]) (n : ℕ) :
    gseq (s*t) n = gseq s n + gseq t n + (s^(p^n)-1)*(t^(p^n)-1)/(p:ℚ_[p])^n := by
  have hpne : (p:ℚ_[p])^n ≠ 0 := by
    apply pow_ne_zero; exact_mod_cast hp.out.ne_zero
  simp only [gseq, mul_pow]
  field_simp
  ring

lemma logp_add (s t : ℚ_[p]) (hs : ‖s - 1‖ ≤ (p:ℝ)⁻¹) (ht : ‖t - 1‖ ≤ (p:ℝ)⁻¹) :
    logp (s * t) = logp s + logp t := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.out.pos
  have hr1 : (p:ℝ)⁻¹ < 1 := by rw [inv_lt_one₀ hp0]; exact_mod_cast hp.out.one_lt
  have hst := norm_mul_sub_one s t hs ht
  have he : Filter.Tendsto (fun n => (s^(p^n)-1)*(t^(p^n)-1)/(p:ℚ_[p])^n) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) (g := fun n => ((p:ℝ)⁻¹)^(n+2))
    · intro n
      rw [norm_div, norm_mul, normp_pow, div_le_iff₀ (by positivity)]
      have hA := pow_pn_bound s hs n
      have hB := pow_pn_bound t ht n
      calc ‖s^(p^n)-1‖ * ‖t^(p^n)-1‖ ≤ ((p:ℝ)⁻¹)^(n+1) * ((p:ℝ)⁻¹)^(n+1) :=
            mul_le_mul hA hB (norm_nonneg _) (by positivity)
        _ = ((p:ℝ)⁻¹)^(n+2) * ((p:ℝ)⁻¹)^n := by ring
    · have : Filter.Tendsto (fun n => ((p:ℝ)⁻¹)^n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr1
      have h2 := this.const_mul (((p:ℝ)⁻¹)^2)
      simp only [mul_zero] at h2
      convert h2 using 2 with n
      rw [pow_add]; ring
  have hsum := (gseq_tendsto s hs).add (gseq_tendsto t ht)
  have htot : Filter.Tendsto (gseq (s*t)) Filter.atTop (nhds (logp s + logp t)) := by
    have := hsum.add he
    rw [add_zero] at this
    refine this.congr (fun n => ?_)
    rw [gseq_mul]
  exact tendsto_nhds_unique (gseq_tendsto (s*t) hst) htot

-- sharp bounds for p odd
lemma pow_step_sharp (hodd : p ≠ 2) (a : ℚ_[p]) (ha : ‖a‖ ≤ (p:ℝ)⁻¹) :
    ‖(1 + a)^p - 1 - (p:ℚ_[p]) * a‖ ≤ (p:ℝ)⁻¹ * ‖a‖^2 := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.out.pos
  have hple1 : (p:ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ hp0]; exact_mod_cast hp.out.one_lt.le
  have ha1 : ‖a‖ ≤ 1 := le_trans ha hple1
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hexp : (1 + a)^p - 1 = ∑ k ∈ Finset.range p, a^(k+1) * (p.choose (k+1) : ℚ_[p]) := by
    have := add_pow a (1:ℚ_[p]) p
    simp only [one_pow, mul_one] at this
    rw [add_comm a 1] at *
    rw [this, Finset.sum_range_succ']; simp
  have hmem : (0:ℕ) ∈ Finset.range p := Finset.mem_range.mpr hp.out.pos
  have hexp2 : (1 + a)^p - 1 - (p:ℚ_[p]) * a
      = ∑ k ∈ (Finset.range p).erase 0, a^(k+1) * (p.choose (k+1) : ℚ_[p]) := by
    rw [hexp, ← Finset.add_sum_erase _ _ hmem]
    simp only [zero_add, pow_one, Nat.choose_one_right]; ring
  rw [hexp2]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro k hk
  simp only [Finset.mem_erase, Finset.mem_range] at hk
  obtain ⟨hk0, hkp'⟩ := hk
  rw [norm_mul, norm_pow]
  have hak2 : ‖a‖^(k+1) ≤ ‖a‖^2 := pow_le_pow_of_le_one (norm_nonneg a) ha1 (by omega)
  rcases Nat.lt_or_ge (k+1) p with hlt | hge
  · have hc : ‖(p.choose (k+1) : ℚ_[p])‖ ≤ (p:ℝ)⁻¹ := norm_choose_le (k+1) (by omega) hlt
    calc ‖a‖^(k+1) * ‖(p.choose (k+1):ℚ_[p])‖ ≤ ‖a‖^2 * (p:ℝ)⁻¹ :=
          mul_le_mul hak2 hc (norm_nonneg _) (by positivity)
      _ = (p:ℝ)⁻¹ * ‖a‖^2 := by ring
  · have hkp : k + 1 = p := by omega
    rw [hkp]
    simp only [Nat.choose_self, Nat.cast_one, norm_one, mul_one]
    have : ‖a‖^p = ‖a‖^(p-2) * ‖a‖^2 := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [this]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc ‖a‖^(p-2) ≤ ((p:ℝ)⁻¹)^(p-2) := pow_le_pow_left₀ (norm_nonneg a) ha _
      _ ≤ ((p:ℝ)⁻¹)^1 := pow_le_pow_of_le_one (by positivity) hple1 (by omega)
      _ = (p:ℝ)⁻¹ := pow_one _

lemma pow_pn_sharp (t : ℚ_[p]) (ht : ‖t - 1‖ ≤ (p:ℝ)⁻¹) (n : ℕ) :
    ‖t^(p^n) - 1‖ ≤ ((p:ℝ)⁻¹)^n * ‖t - 1‖ := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.out.pos
  have hple1 : (p:ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ hp0]; exact_mod_cast hp.out.one_lt.le
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : ‖t^(p^n) - 1‖ ≤ (p:ℝ)⁻¹ := le_trans (pow_pn_bound t ht n) (by
      calc ((p:ℝ)⁻¹)^(n+1) ≤ ((p:ℝ)⁻¹)^1 := pow_le_pow_of_le_one (by positivity) hple1 (by omega)
        _ = (p:ℝ)⁻¹ := pow_one _)
    have hrw : t^(p^(n+1)) = (1 + (t^(p^n) - 1))^p := by
      rw [show (1 + (t^(p^n) - 1)) = t^(p^n) by ring, ← pow_mul, pow_succ]
    rw [hrw]
    refine le_trans (pow_step (t^(p^n) - 1) hs) ?_
    calc (p:ℝ)⁻¹ * ‖t^(p^n) - 1‖ ≤ (p:ℝ)⁻¹ * (((p:ℝ)⁻¹)^n * ‖t-1‖) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ = ((p:ℝ)⁻¹)^(n+1) * ‖t-1‖ := by rw [pow_succ]; ring

lemma gseq_zero (t : ℚ_[p]) : gseq t 0 = t - 1 := by simp [gseq]

lemma sharp_cauchy_step (hodd : p ≠ 2) (t : ℚ_[p]) (ht : ‖t - 1‖ ≤ (p:ℝ)⁻¹) (n : ℕ) :
    ‖gseq t (n+1) - gseq t n‖ ≤ ((p:ℝ)⁻¹)^n * ‖t - 1‖^2 := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.out.pos
  set a := t^(p^n) - 1 with ha_def
  have hta : t^(p^n) = 1 + a := by rw [ha_def]; ring
  have habound : ‖a‖ ≤ ((p:ℝ)⁻¹)^n * ‖t-1‖ := pow_pn_sharp t ht n
  have hale : ‖a‖ ≤ (p:ℝ)⁻¹ := le_trans (pow_pn_bound t ht n) (by
      calc ((p:ℝ)⁻¹)^(n+1) ≤ ((p:ℝ)⁻¹)^1 :=
            pow_le_pow_of_le_one (by positivity) (by rw [inv_le_one₀ hp0]; exact_mod_cast hp.out.one_lt.le) (by omega)
        _ = (p:ℝ)⁻¹ := pow_one _)
  have key : gseq t (n+1) - gseq t n = ((1+a)^p - 1 - (p:ℚ_[p])*a) / (p:ℚ_[p])^(n+1) := by
    have e1 : t^(p^(n+1)) = (1+a)^p := by
      rw [show p^(n+1) = p^n * p by rw [pow_succ], pow_mul, ← hta]
    simp only [gseq]
    rw [e1, ha_def]
    have hpne : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    field_simp; ring
  rw [key, norm_div, normp_pow, div_le_iff₀ (by positivity)]
  calc ‖(1+a)^p - 1 - (p:ℚ_[p])*a‖ ≤ (p:ℝ)⁻¹ * ‖a‖^2 := pow_step_sharp hodd a hale
    _ ≤ (p:ℝ)⁻¹ * (((p:ℝ)⁻¹)^n * ‖t-1‖)^2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (norm_nonneg a) habound
    _ = ((p:ℝ)⁻¹)^n * ‖t-1‖^2 * ((p:ℝ)⁻¹)^(n+1) := by rw [pow_succ]; ring

lemma gseq_sub_le (hodd : p ≠ 2) (t : ℚ_[p]) (ht : ‖t - 1‖ ≤ (p:ℝ)⁻¹) (n : ℕ) :
    ‖gseq t n - (t-1)‖ ≤ ‖t - 1‖^2 := by
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.out.pos
  have hple1 : (p:ℝ)⁻¹ ≤ 1 := by rw [inv_le_one₀ hp0]; exact_mod_cast hp.out.one_lt.le
  induction n with
  | zero => simp only [gseq_zero, sub_self, norm_zero]; positivity
  | succ n ih =>
    have h1 : ‖gseq t (n+1) - gseq t n‖ ≤ ‖t-1‖^2 := by
      refine le_trans (sharp_cauchy_step hodd t ht n) ?_
      calc ((p:ℝ)⁻¹)^n * ‖t-1‖^2 ≤ 1 * ‖t-1‖^2 :=
            mul_le_mul_of_nonneg_right (by
              calc ((p:ℝ)⁻¹)^n ≤ ((p:ℝ)⁻¹)^0 := pow_le_pow_of_le_one (by positivity) hple1 (by omega)
                _ = 1 := pow_zero _) (by positivity)
        _ = ‖t-1‖^2 := by ring
    calc ‖gseq t (n+1) - (t-1)‖ = ‖(gseq t (n+1) - gseq t n) + (gseq t n - (t-1))‖ := by ring_nf
      _ ≤ max ‖gseq t (n+1) - gseq t n‖ ‖gseq t n - (t-1)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ ‖t-1‖^2 := max_le h1 ih

lemma logp_sub_le (hodd : p ≠ 2) (t : ℚ_[p]) (ht : ‖t - 1‖ ≤ (p:ℝ)⁻¹) :
    ‖logp t - (t-1)‖ ≤ ‖t - 1‖^2 := by
  have htend : Filter.Tendsto (fun n => gseq t n - (t-1)) Filter.atTop (nhds (logp t - (t-1))) :=
    (gseq_tendsto t ht).sub_const _
  have hcont : Filter.Tendsto (fun n => ‖gseq t n - (t-1)‖) Filter.atTop (nhds ‖logp t - (t-1)‖) :=
    (continuous_norm.tendsto _).comp htend
  exact le_of_tendsto hcont (Filter.Eventually.of_forall (fun n => gseq_sub_le hodd t ht n))

lemma logp_one : logp (1 : ℚ_[p]) = 0 := by
  have : gseq (1:ℚ_[p]) = fun _ => 0 := by
    funext n; show ((1:ℚ_[p])^(p^n) - 1)/(p:ℚ_[p])^n = 0
    rw [one_pow, sub_self, zero_div]
  unfold logp; rw [this]; exact tendsto_const_nhds.limUnder_eq

lemma norm_unit_eq_one (t : ℚ_[p]) (ht : ‖t - 1‖ ≤ (p:ℝ)⁻¹) : ‖t‖ = 1 := by
  have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.out.one_lt
  have hlt : ‖t - 1‖ < 1 := lt_of_le_of_lt ht (by simpa using inv_lt_one_of_one_lt₀ hp1)
  refine le_antisymm (norm_one_unit t ht) ?_
  by_contra hlt2
  push_neg at hlt2
  have key : ‖t - (t-1)‖ ≤ max ‖t‖ ‖t - 1‖ := by
    have hmm := IsUltrametricDist.norm_add_le_max t (-(t-1))
    rw [norm_neg] at hmm
    calc ‖t - (t-1)‖ = ‖t + (-(t-1))‖ := by ring_nf
      _ ≤ max ‖t‖ ‖t-1‖ := hmm
  have hh : (1:ℝ) ≤ max ‖t‖ ‖t - 1‖ := by
    have h1 : t - (t-1) = (1:ℚ_[p]) := by ring
    rw [h1, norm_one] at key; exact key
  rcases max_cases ‖t‖ ‖t-1‖ with ⟨h,_⟩ | ⟨h,_⟩ <;> rw [h] at hh <;> linarith

lemma norm_pow_sub_one (t : ℚ_[p]) (ht : ‖t - 1‖ ≤ (p:ℝ)⁻¹) (k : ℕ) : ‖t^k - 1‖ ≤ (p:ℝ)⁻¹ := by
  induction k with
  | zero => simp only [pow_zero, sub_self, norm_zero]; positivity
  | succ k ih => rw [pow_succ]; exact norm_mul_sub_one _ _ ih ht

lemma norm_inv_sub_one (t : ℚ_[p]) (ht : ‖t - 1‖ ≤ (p:ℝ)⁻¹) : ‖t⁻¹ - 1‖ ≤ (p:ℝ)⁻¹ := by
  have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.out.one_lt
  have htne : t ≠ 0 := by
    intro h; rw [h] at ht; simp only [zero_sub, norm_neg, norm_one] at ht
    linarith [inv_lt_one_of_one_lt₀ hp1]
  have ht1 : ‖t‖ = 1 := norm_unit_eq_one t ht
  have heq : t⁻¹ - 1 = -(t - 1) * t⁻¹ := by field_simp; ring
  rw [heq, norm_mul, norm_neg, norm_inv, ht1, inv_one, mul_one]
  exact ht

lemma logp_inv (t : ℚ_[p]) (ht : ‖t - 1‖ ≤ (p:ℝ)⁻¹) : logp t⁻¹ = - logp t := by
  have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.out.one_lt
  have htne : t ≠ 0 := by
    intro h; rw [h] at ht; simp only [zero_sub, norm_neg, norm_one] at ht
    linarith [inv_lt_one_of_one_lt₀ hp1]
  have hadd := logp_add t t⁻¹ ht (norm_inv_sub_one t ht)
  rw [mul_inv_cancel₀ htne, logp_one] at hadd
  linear_combination -hadd

lemma logp_pow (t : ℚ_[p]) (ht : ‖t - 1‖ ≤ (p:ℝ)⁻¹) (k : ℕ) : logp (t^k) = k • logp t := by
  induction k with
  | zero => simp [logp_one]
  | succ k ih =>
    rw [pow_succ, logp_add _ _ (norm_pow_sub_one t ht k) ht, ih, succ_nsmul]

-- finite expansion of the log-sequence: gseq(1+u) n = ∑_{k=1}^{p^n} (C(p^n,k)/p^n) u^k
lemma gseq_expand (u : ℚ_[p]) (n : ℕ) :
    gseq (1 + u) n = ∑ k ∈ Finset.range (p^n), u^(k+1) * ((p^n).choose (k+1) : ℚ_[p]) / (p:ℚ_[p])^n := by
  have hpn : (p:ℚ_[p])^n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  rw [gseq]
  rw [show (1+u)^(p^n) = ∑ k ∈ Finset.range (p^n), u^(k+1) * ((p^n).choose (k+1) : ℚ_[p]) + 1 by
    have h := add_pow u (1:ℚ_[p]) (p^n)
    simp only [one_pow, mul_one] at h
    rw [add_comm (1:ℚ_[p]) u, h, Finset.sum_range_succ']
    simp]
  rw [add_sub_cancel_right, Finset.sum_div]
