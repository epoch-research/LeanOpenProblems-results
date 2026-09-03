import Submission.SquareRootFluctuationExplore

/-! Square-root fluctuations forced by a putative witness, without assuming
that its normalized squared error converges. These necessary conditions do
not disprove the logarithmic representation conjecture. -/
namespace Erdos66FrequentFluctuation
open Filter AdditiveCombinatorics Erdos66Fractional Erdos66Generating
  Erdos66FractionalFourthPower Erdos66SquareRootFluctuation Erdos66ResidueSeries
open scoped Topology Classical

noncomputable def normalizedMassGap (A : Set ℕ) (c r : ℝ) : ℝ :=
  (max 0 (series (indicator A) (r^2)*Real.sqrt (kernel r) -
    c*(series (fun n ↦ (profile n)^2) r*Real.sqrt (kernel r))))^2

lemma normalizedMassGap_limit {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (normalizedMassGap A c) (𝓝[<] 1) (𝓝 (c/2)) := by
  have hcpos := Erdos66Explore.limit_pos hc h
  have hleft0 := (doubled_radius_limit hc h).sub (profile_square_series_limit.const_mul c)
  simp only [mul_zero,sub_zero] at hleft0
  have hleft := ((show Tendsto (fun _ : ℝ ↦ (0 : ℝ)) (𝓝[<] 1) (𝓝 0) from
    tendsto_const_nhds).max hleft0).pow 2
  have hspos : 0 < Real.sqrt c/Real.sqrt 2 :=
    div_pos (Real.sqrt_pos.mpr hcpos) (by positivity)
  rw [max_eq_right hspos.le,div_pow,Real.sq_sqrt hcpos.le,
    Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] at hleft
  exact hleft

lemma normalizedMassGap_le {A : Set ℕ} {c r : ℝ}
    (hc : 0 ≤ c) (hr0 : 0 < r) (hr1 : r < 1)
    (hE : Summable (fun n ↦ ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2*r^n)) :
    normalizedMassGap A c r ≤
      series (fun n ↦ ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2) r * kernel r := by
  have hk := (kernel_pos hr0 hr1).le
  have hb := mul_le_mul_of_nonneg_right
    (weighted_error_lower_bound hc hr0 hr1 hE) hk
  have hs := Real.sq_sqrt hk
  unfold normalizedMassGap
  calc
    _ = (max 0 (series (indicator A) (r^2)-c*series (fun n ↦ (profile n)^2) r) *
        Real.sqrt (kernel r))^2 := by
      rw [max_mul_of_nonneg _ _ (Real.sqrt_nonneg _),zero_mul,sub_mul]
      congr 2
      ring
    _ = _ := by rw [mul_pow,hs]
    _ ≤ _ := hb

/-- Any eventual envelope of the squared error, with logarithmic limiting
coefficient d, has d at least c/2. The squared error need not have a limit. -/
theorem error_envelope_limit_lower_bound {A : Set ℕ} {c d : ℝ} {f : ℕ → ℝ}
    (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (hf : Tendsto (fun n ↦ f n/Real.log n) atTop (𝓝 d))
    (hdom : ∀ᶠ n : ℕ in atTop,
      ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2 ≤ f n) : c/2 ≤ d := by
  let e : ℕ → ℝ := fun n ↦ ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2
  let g : ℕ → ℝ := fun n ↦ max (e n) (f n)
  have hg : Tendsto (fun n ↦ g n/Real.log n) atTop (𝓝 d) := by
    apply hf.congr'
    filter_upwards [hdom] with n hn
    simp only [g,e,max_eq_right hn]
  have hgs {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
      Summable (fun n ↦ g n*r^n) := summable_of_log_limit hg hr0 hr1
  have hes {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
      Summable (fun n ↦ e n*r^n) := by
    apply (hgs hr0 hr1).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hr0.le n))]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hr0.le n)
  have hright : Tendsto (fun r : ℝ ↦ series g r * kernel r) (𝓝[<] 1) (𝓝 d) := by
    simpa only [kernel,mul_div_assoc] using logarithmic_abelian_limit hg
      (fun r hr0 hr1 ↦ hgs hr0 hr1)
  apply le_of_tendsto_of_tendsto (normalizedMassGap_limit hc h) hright
  filter_upwards [unit_interval_eventually] with r hr
  have he_le : series e r ≤ series g r := by
    exact (hes hr.1 hr.2).tsum_le_tsum
      (fun n ↦ mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hr.1.le n))
      (hgs hr.1 hr.2)
  exact (normalizedMassGap_le (Erdos66Explore.limit_pos hc h).le hr.1 hr.2
    (hes hr.1 hr.2)).trans
      (mul_le_mul_of_nonneg_right he_le (kernel_pos hr.1 hr.2).le)

lemma eventual_squared_error_bound {A : Set ℕ} {c d : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (he : ∀ᶠ n : ℕ in atTop,
      ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2/Real.log n ≤ d) : c/2 ≤ d := by
  have hf : Tendsto (fun n : ℕ ↦ (d*Real.log n)/Real.log n) atTop (𝓝 d) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hl : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
    exact (mul_div_cancel_right₀ d hl).symm
  apply error_envelope_limit_lower_bound hc h hf
  filter_upwards [he,eventually_ge_atTop 2] with n hn hn2
  exact (div_le_iff₀ (Real.log_pos (by exact_mod_cast hn2))).mp hn

/-- Arbitrarily large targets have squared normalized deviation greater than
any prescribed d<c/2. -/
theorem frequently_squared_error_gt {A : Set ℕ} {c d : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (hd : d < c/2) :
    ∃ᶠ n : ℕ in atTop,
      d < ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2/Real.log n := by
  by_contra hh
  have he : ∀ᶠ n : ℕ in atTop,
      ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2/Real.log n ≤ d := by
    simpa only [not_lt] using not_frequently.mp hh
  exact (not_le.mpr hd) (eventual_squared_error_bound hc h he)

/-- In particular no witness has harmonic-centered fluctuations eventually
bounded by a*sqrt(log n) when a is nonnegative and a²<c/2. -/
theorem frequently_abs_harmonic_error_gt {A : Set ℕ} {c a : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (ha : 0 ≤ a) (ha2 : a^2 < c/2) :
    ∃ᶠ n : ℕ in atTop,
      a*Real.sqrt (Real.log n) < |(sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ)| := by
  apply ((frequently_squared_error_gt hc h ha2).and_eventually
    (eventually_ge_atTop 2)).mono
  intro n hn
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn.2)
  apply (sq_lt_sq₀ (mul_nonneg ha (Real.sqrt_nonneg _)) (abs_nonneg _)).mp
  rw [sq_abs,mul_pow,Real.sq_sqrt hl.le]
  exact (lt_div_iff₀ hl).mp hn.1

lemma harmonic_shift_sub_log_limit :
    Tendsto (fun n : ℕ ↦ (harmonic (n+1) : ℝ)-Real.log n) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
  have hh := Real.tendsto_harmonic_sub_log.add
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simp only [add_zero] at hh
  convert hh using 1
  funext n
  rw [harmonic_succ]
  push_cast
  rw [one_div]
  ring

lemma harmonic_log_center_difference_limit (c : ℝ) :
    Tendsto (fun n : ℕ ↦ |c*((harmonic (n+1) : ℝ)-Real.log n)| /
      Real.sqrt (Real.log n)) atTop (𝓝 0) := by
  exact (harmonic_shift_sub_log_limit.const_mul c).abs.div_atTop
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

/-- The same fluctuation lower bound holds with the conjecture's natural
center c*log n in place of the exact harmonic model. -/
theorem frequently_abs_log_error_gt {A : Set ℕ} {c a : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (ha : 0 ≤ a) (ha2 : a^2 < c/2) :
    ∃ᶠ n : ℕ in atTop,
      a*Real.sqrt (Real.log n) < |(sumRep A n : ℝ)-c*Real.log n| := by
  have hcpos := Erdos66Explore.limit_pos hc h
  have hhalf : 0 ≤ c/2 := by positivity
  have hasqrt : a < Real.sqrt (c/2) := by
    apply (sq_lt_sq₀ ha (Real.sqrt_nonneg _)).mp
    rwa [Real.sq_sqrt hhalf]
  obtain ⟨b,hab,hbsqrt⟩ := exists_between hasqrt
  have hb : 0 ≤ b := ha.trans hab.le
  have hb2 : b^2 < c/2 := by
    simpa only [Real.sq_sqrt hhalf] using
      (sq_lt_sq₀ hb (Real.sqrt_nonneg (c/2))).mpr hbsqrt
  have hclose := (harmonic_log_center_difference_limit c).eventually
    (gt_mem_nhds (sub_pos.mpr hab))
  apply (((frequently_abs_harmonic_error_gt hc h hb hb2).and_eventually hclose).and_eventually
    (eventually_ge_atTop 2)).mono
  intro n hn
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn.2)
  have hs : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hl
  have hdist := (div_lt_iff₀ hs).mp hn.1.2
  have htri := abs_sub_le (sumRep A n : ℝ) (c*Real.log n) (c*(harmonic (n+1) : ℝ))
  have heq : |c*Real.log n-c*(harmonic (n+1) : ℝ)| =
      |c*((harmonic (n+1) : ℝ)-Real.log n)| := by
    rw [abs_sub_comm,← mul_sub]
  rw [heq] at htri
  nlinarith [hn.1.1]

/-- Explicit arbitrarily-large-target form of the log-centered result. -/
theorem exists_large_log_fluctuation {A : Set ℕ} {c a : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (ha : 0 ≤ a) (ha2 : a^2 < c/2) (N : ℕ) :
    ∃ n ≥ N, a*Real.sqrt (Real.log n) < |(sumRep A n : ℝ)-c*Real.log n| :=
  frequently_atTop.mp (frequently_abs_log_error_gt hc h ha ha2) N

end Erdos66FrequentFluctuation
