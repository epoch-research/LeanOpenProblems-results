import Submission.SharpFluctuationExplore

/-! A direct lower bound for the Abel-averaged squared representation error.
Unlike the earlier envelope theorem, it needs no auxiliary convergence or
pointwise bound for that squared error. It remains only a necessary condition. -/
namespace Erdos66AbelErrorEnergy
open Filter AdditiveCombinatorics Erdos66Generating Erdos66Fractional
  Erdos66FractionalFourthPower Erdos66SharpFluctuation Erdos66ResidueSeries
open scoped Topology Classical
set_option maxHeartbeats 1500000

noncomputable def errorSq (A : Set ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))^2

lemma summable_errorSq (A : Set ℕ) (c : ℝ) {r : ℝ} (hr0 : 0≤r) (hr1 : r<1) :
    Summable (fun n ↦ errorSq A c n*r^n) := by
  have hnr : ‖r‖<1 := by simpa [Real.norm_eq_abs,abs_of_nonneg hr0] using hr1
  have hpoly := ((summable_pow_mul_geometric_of_norm_lt_one 2 hnr).add
    ((summable_pow_mul_geometric_of_norm_lt_one 1 hnr).mul_left (2 : ℝ))).add
      (summable_geometric_of_lt_one hr0 hr1)
  have hdom := hpoly.mul_left ((1+|c|)^2)
  apply hdom.of_norm_bounded
  intro n
  have hs : (sumRep A n : ℝ)≤(n : ℝ)+1 := by
    exact_mod_cast Erdos66Counting.sumRep_le_succ A n
  have hh : (harmonic (n+1) : ℝ)≤(n : ℝ)+1 := by
    simpa only [Nat.cast_add,Nat.cast_one] using harmonic_le_nat (n+1)
  have hnon := harmonic_nonneg (n+1)
  have habs : |(sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ)|≤(1+|c|)*((n : ℝ)+1) := by
    calc
      _ ≤ |(sumRep A n : ℝ)|+|c*(harmonic (n+1) : ℝ)| := abs_sub _ _
      _ = (sumRep A n : ℝ)+|c| *(harmonic (n+1) : ℝ) := by
        rw [abs_of_nonneg (Nat.cast_nonneg _),abs_mul,abs_of_nonneg hnon]
      _ ≤ (n : ℝ)+1+|c| *((n : ℝ)+1) := add_le_add hs (mul_le_mul_of_nonneg_left hh (abs_nonneg _))
      _ = _ := by ring
  have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr habs
  rw [sq_abs] at hsq
  rw [Real.norm_eq_abs,abs_of_nonneg (by unfold errorSq; positivity)]
  calc
    _ ≤ ((1+|c|)*((n : ℝ)+1))^2*r^n :=
      mul_le_mul_of_nonneg_right hsq (pow_nonneg hr0 n)
    _ = _ := by ring

lemma root_tendsto_one_left (m : ℕ) (hm : m≠0) :
    Tendsto (fun r : ℝ ↦ r^((m : ℝ)⁻¹)) (𝓝[<] 1) (𝓝[<] 1) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hh : Tendsto (fun r : ℝ ↦ r) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_right nhdsWithin_le_nhds
    simpa only [Real.one_rpow] using hh.rpow_const (Or.inl one_ne_zero)
  · filter_upwards [unit_interval_eventually] with r hr
    exact Real.rpow_lt_one hr.1.le hr.2 (inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hm))

lemma eventually_of_eventually_power (P : ℝ→Prop) (m : ℕ) (hm : m≠0)
    (hP : ∀ᶠ r : ℝ in 𝓝[<] 1, P (r^m)) : ∀ᶠ r : ℝ in 𝓝[<] 1, P r := by
  filter_upwards [(root_tendsto_one_left m hm).eventually hP,unit_interval_eventually] with r hr hunit
  simpa only [Real.rpow_inv_natCast_pow hunit.1.le hm] using hr

lemma tilted_gap_limit {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) (k : ℕ) :
    Tendsto (fun r : ℝ ↦
      (max 0 (series (indicator A) (r^(2*k+2))-c*series (fun n ↦ (profile n)^2) (r^(2*k+1))))^2*
        kernel r) (𝓝[<] 1) (𝓝 (c/((2*k+2 : ℕ) : ℝ))) := by
  have hcpos := Erdos66Explore.limit_pos hc h
  have hh := (normalized_indicator_power_limit hc h (2*k+2) (by omega)).sub
    ((normalized_profile_square_power_limit (2*k+1) (by omega)).const_mul c)
  simp only [mul_zero,sub_zero] at hh
  have hlim := ((show Tendsto (fun _ : ℝ ↦ (0 : ℝ)) (𝓝[<] 1) (𝓝 0) from tendsto_const_nhds).max hh).pow 2
  have hpos : 0<Real.sqrt c/Real.sqrt ((2*k+2 : ℕ) : ℝ) := by positivity
  rw [max_eq_right hpos.le,div_pow,Real.sq_sqrt hcpos.le,
    Real.sq_sqrt (by positivity : (0 : ℝ)≤((2*k+2 : ℕ) : ℝ))] at hlim
  apply hlim.congr'
  filter_upwards [unit_interval_eventually] with r hr
  have hk := (kernel_pos hr.1 hr.2).le
  have he : max 0 (series (indicator A) (r^(2*k+2))*Real.sqrt (kernel r)-
      c*(series (fun n ↦ (profile n)^2) (r^(2*k+1))*Real.sqrt (kernel r))) =
      max 0 (series (indicator A) (r^(2*k+2))-c*series (fun n ↦ (profile n)^2) (r^(2*k+1)))*
        Real.sqrt (kernel r) := by
    rw [max_mul_of_nonneg _ _ (Real.sqrt_nonneg _),zero_mul,sub_mul]
    congr 1
    ring
  rw [he,mul_pow,Real.sq_sqrt hk]

/-- The sharp coefficient c is a lower limit of the normalized Abel error
energy. No convergence assumption for the error energy is used. -/
theorem normalized_error_energy_eventually_gt {A : Set ℕ} {c d : ℝ} (hc : c≠0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) (hd : d<c) :
    ∀ᶠ r : ℝ in 𝓝[<] 1, d<series (errorSq A c) r*kernel r := by
  have hcpos := Erdos66Explore.limit_pos hc h
  obtain ⟨k,hk⟩ := exists_nat_gt ((2*d-c)/(2*(c-d)))
  have hcoeff : d<c/((2*k+2 : ℕ) : ℝ)*((2*k+1 : ℕ) : ℝ) := by
    have hh := (div_lt_iff₀ (by linarith : 0<2*(c-d))).mp hk
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ)<((2*k+2 : ℕ) : ℝ))).mpr
    push_cast at *
    nlinarith
  have hleft := (tilted_gap_limit hc h k).mul (power_kernel_ratio (2*k+1) (by omega))
  have hlarge := hleft.eventually (lt_mem_nhds hcoeff)
  apply eventually_of_eventually_power _ (2*k+1) (by omega)
  filter_upwards [hlarge,unit_interval_eventually] with r hr hunit
  have hrm0 : 0<r^(2*k+1) := pow_pos hunit.1 _
  have hrm1 : r^(2*k+1)<1 := pow_lt_one₀ hunit.1.le hunit.2 (by omega)
  have hb := tilted_weighted_lower_bound k hcpos.le hunit.1 hunit.2
    (summable_errorSq A c hrm0.le hrm1)
  change _≤series (errorSq A c) (r^(2*k+1)) at hb
  have hkm := (kernel_pos hrm0 hrm1).le
  have hkr := (kernel_pos hunit.1 hunit.2).ne'
  have hh := mul_le_mul_of_nonneg_right hb hkm
  apply hr.trans_le
  convert hh using 1 <;> field_simp

lemma square_sum_le (x y t : ℝ) (ht : 0<t) :
    (x+y)^2≤(1+t)*x^2+(1+1/t)*y^2 := by
  have hh := sq_nonneg (t*x-y)
  have he : t*(1+1/t)=t+1 := by field_simp
  have hres : t*((x+y)^2)≤t*((1+t)*x^2+(1+1/t)*y^2) := by
    rw [mul_add,←mul_assoc t (1+t),←mul_assoc t (1+1/t),he]
    nlinarith
  exact (mul_le_mul_iff_right₀ ht).mp hres

/-- Changing the center by a sequence whose squared discrepancy is o(log n)
does not change the sharp lower coefficient of the Abel error energy. -/
theorem perturbed_center_energy_eventually_gt {A : Set ℕ} {c d : ℝ} (hc : c≠0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (g : ℕ→ℝ)
    (hg : Tendsto (fun n ↦ (g n-c*(harmonic (n+1) : ℝ))^2/Real.log n) atTop (𝓝 0))
    (hd : d<c) :
    ∀ᶠ r : ℝ in 𝓝[<] 1,
      d<series (fun n ↦ ((sumRep A n : ℝ)-g n)^2) r*kernel r := by
  let δ : ℕ→ℝ := fun n ↦ (g n-c*(harmonic (n+1) : ℝ))^2
  have hδs (r : ℝ) (hr0 : 0<r) (hr1 : r<1) : Summable (fun n ↦ δ n*r^n) :=
    summable_of_log_limit hg hr0 hr1
  have hgs (r : ℝ) (hr0 : 0<r) (hr1 : r<1) :
      Summable (fun n ↦ ((sumRep A n : ℝ)-g n)^2*r^n) := by
    apply (((summable_errorSq A c hr0.le hr1).mul_left 2).add ((hδs r hr0 hr1).mul_left 2)).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hh := square_sum_le ((sumRep A n : ℝ)-c*(harmonic (n+1) : ℝ))
      (c*(harmonic (n+1) : ℝ)-g n) 1 (by norm_num)
    have he : ((sumRep A n : ℝ)-g n)^2≤2*errorSq A c n+2*δ n := by
      dsimp [errorSq,δ]
      nlinarith
    calc
      _ ≤ (2*errorSq A c n+2*δ n)*r^n := mul_le_mul_of_nonneg_right he (pow_nonneg hr0.le n)
      _ = _ := by ring
  have hδlim : Tendsto (fun r : ℝ ↦ series δ r*kernel r) (𝓝[<] 1) (𝓝 0) := by
    simpa only [kernel,mul_div_assoc] using logarithmic_abelian_limit hg hδs
  by_cases hdneg : d<0
  · filter_upwards [unit_interval_eventually] with r hr
    exact hdneg.trans_le (mul_nonneg (tsum_nonneg (fun n ↦ mul_nonneg (sq_nonneg _) (pow_nonneg hr.1.le n))) (kernel_pos hr.1 hr.2).le)
  have hd0 : 0≤d := le_of_not_gt hdneg
  let t : ℝ := (c-d)/(4*(d+1))
  have ht : 0<t := div_pos (by linarith) (by positivity)
  have htd : t*(4*(d+1))=c-d := div_mul_cancel₀ _ (by positivity)
  let e : ℝ := (c+d)/2
  have hec : e<c := by dsimp [e]; linarith
  have hetd : (1+t)*d<e := by dsimp [e]; nlinarith
  have hsmall := (hδlim.const_mul (1+1/t)).eventually_lt_const (show (1+1/t)*0<e-(1+t)*d by simpa using sub_pos.mpr hetd)
  filter_upwards [normalized_error_energy_eventually_gt hc h hec,hsmall,unit_interval_eventually]
    with r hrE hrδ hr
  have hpoint (n : ℕ) : errorSq A c n≤(1+t)*((sumRep A n : ℝ)-g n)^2+(1+1/t)*δ n := by
    have hh := square_sum_le ((sumRep A n : ℝ)-g n) (g n-c*(harmonic (n+1) : ℝ)) t ht
    convert hh using 1 <;> dsimp [errorSq,δ] <;> ring
  have hsum := (summable_errorSq A c hr.1.le hr.2).tsum_le_tsum
    (fun n ↦ mul_le_mul_of_nonneg_right (hpoint n) (pow_nonneg hr.1.le n))
    ((((hgs r hr.1 hr.2).mul_left (1+t)).add ((hδs r hr.1 hr.2).mul_left (1+1/t))).congr
      (fun n ↦ by ring))
  have heq : (∑' n, ((1+t)*((sumRep A n : ℝ)-g n)^2+(1+1/t)*δ n)*r^n) =
      (1+t)*series (fun n ↦ ((sumRep A n : ℝ)-g n)^2) r+(1+1/t)*series δ r := by
    calc
      _ = (∑' n, ((1+t)*(((sumRep A n : ℝ)-g n)^2*r^n)+(1+1/t)*(δ n*r^n))) :=
        tsum_congr (fun n ↦ by ring)
      _ = _ := by
        rw [Summable.tsum_add ((hgs r hr.1 hr.2).mul_left (1+t)) ((hδs r hr.1 hr.2).mul_left (1+1/t)),
          tsum_mul_left,tsum_mul_left]
        rfl
  rw [heq] at hsum
  have hh := mul_le_mul_of_nonneg_right hsum (kernel_pos hr.1 hr.2).le
  change series (errorSq A c) r*kernel r≤_ at hh
  nlinarith

/-- The direct Abel lower bound at the conjecture's logarithmic center. -/
theorem logarithmic_error_energy_eventually_gt {A : Set ℕ} {c d : ℝ} (hc : c≠0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) (hd : d<c) :
    ∀ᶠ r : ℝ in 𝓝[<] 1,
      d<series (fun n ↦ ((sumRep A n : ℝ)-c*Real.log n)^2) r*kernel r := by
  apply perturbed_center_energy_eventually_gt hc h (fun n ↦ c*Real.log n) ?_ hd
  have hh := ((Erdos66FrequentFluctuation.harmonic_shift_sub_log_limit.const_mul c).pow 2).div_atTop
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  convert hh using 1
  funext n
  congr 1
  ring

end Erdos66AbelErrorEnergy
