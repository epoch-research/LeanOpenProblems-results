import Submission.RawHarmonicTauberian

/-! A bounded-sequence Tauberian criterion using short multiplicative windows.
The cancellation hypotheses below are not asserted for the prime comparison. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

lemma rawHarmonicSum_window (f : ℕ → ℝ) (L U : ℕ) (hLU : L≤U) :
    rawHarmonicSum f U-rawHarmonicSum f L =
      ∑ n ∈ Ico L U, f n/(n : ℝ) :=
  (sum_Ico_eq_sub _ hLU).symm

lemma harmonic_window_unweighting_error (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1)
    (L U : ℕ) (hL : 0<L) (hLU : L≤U) :
    |(∑ n ∈ Ico L U, f n) - (L : ℝ)*(rawHarmonicSum f U-rawHarmonicSum f L)| ≤
      (U-L : ℕ)^2/(L : ℝ) := by
  have hLr : (0 : ℝ)<L := by exact_mod_cast hL
  rw [rawHarmonicSum_window f L U hLU, mul_sum, ← sum_sub_distrib]
  have hb (n : ℕ) (hn : n∈Ico L U) :
      |f n-(L : ℝ)*(f n/n)| ≤ (U-L : ℕ)/(L : ℝ) := by
    have hnL : (L : ℝ)≤n := by exact_mod_cast (mem_Ico.mp hn).1
    have hnU : (n : ℝ)≤U := by exact_mod_cast (mem_Ico.mp hn).2.le
    have hnr : (0 : ℝ)<n := hLr.trans_le hnL
    have he : f n-(L : ℝ)*(f n/n)=f n*((n-L : ℝ)/n) := by field_simp
    rw [he,abs_mul,abs_div,abs_of_nonneg (sub_nonneg.mpr hnL),abs_of_pos hnr]
    calc
      _ ≤ 1*((n-L : ℝ)/n) := mul_le_mul_of_nonneg_right (hf n) (div_nonneg (sub_nonneg.mpr hnL) hnr.le)
      _ ≤ (U-L : ℝ)/L := by
        rw [one_mul]
        exact div_le_div₀ (sub_nonneg.mpr (hnL.trans hnU)) (by linarith) hLr hnL
      _ = _ := by rw [Nat.cast_sub hLU]
  calc
    _ ≤ ∑ n ∈ Ico L U, |f n-(L : ℝ)*(f n/n)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Ico L U, (U-L : ℕ)/(L : ℝ) := sum_le_sum hb
    _ = _ := by simp only [sum_const,Nat.card_Ico,nsmul_eq_mul]; ring

lemma prefixMean_harmonic_window_bound (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1)
    (L U : ℕ) (hL : 0<L) (hLU : L≤U) :
    |prefixMean U f| ≤ (L : ℝ)/U*|prefixMean L f|+
      (L : ℝ)/U*|rawHarmonicSum f U-rawHarmonicSum f L|+
        (U-L : ℕ)^2/((L : ℝ)*U) := by
  have hLr : (0 : ℝ)<L := by exact_mod_cast hL
  have hUr : (0 : ℝ)<U := by exact_mod_cast hL.trans_le hLU
  let D := rawHarmonicSum f U-rawHarmonicSum f L
  let E := (∑ n ∈ Ico L U, f n)-(L : ℝ)*D
  have he : prefixMean U f = (L : ℝ)/U*prefixMean L f+(L : ℝ)/U*D+E/U := by
    dsimp [prefixMean,E,D]
    rw [sum_Ico_eq_sub _ hLU]
    field_simp
    ring
  have hE : |E|≤(U-L : ℕ)^2/(L : ℝ) := harmonic_window_unweighting_error f hf L U hL hLU
  rw [he]
  calc
    _ ≤ |(L : ℝ)/U*prefixMean L f|+|(L : ℝ)/U*D|+|E/U| := abs_add_three _ _ _
    _ ≤ _ := by
      simp only [abs_mul,abs_div,abs_of_pos hUr,abs_of_pos hLr]
      dsimp only [D] at *
      apply add_le_add le_rfl
      simpa only [div_div] using div_le_div_of_nonneg_right hE hUr.le

lemma prefixMean_scaled_harmonic_window_bound (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1)
    (a b N : ℕ) (hb : 0<b) (hba : b≤a) (hN : 0<N) :
    |prefixMean (a*N) f| ≤ (b : ℝ)/a*|prefixMean (b*N) f|+
      (b : ℝ)/a*|rawHarmonicSum f (a*N)-rawHarmonicSum f (b*N)|+
        ((a : ℝ)-b)^2/((a : ℝ)*b) := by
  have h := prefixMean_harmonic_window_bound f hf (b*N) (a*N)
    (Nat.mul_pos hb hN) (Nat.mul_le_mul_right N hba)
  have hNr : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
  have har : (a : ℝ)≠0 := by exact_mod_cast (hb.trans_le hba).ne'
  have hbr : (b : ℝ)≠0 := by exact_mod_cast hb.ne'
  rw [Nat.cast_sub (Nat.mul_le_mul_right N hba)] at h
  push_cast at h
  convert h using 1
  all_goals field_simp

lemma abs_prefixMean_bounded (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1) (N : ℕ) :
    |prefixMean N f|≤1 := by
  rcases N with _|N
  · simp [prefixMean]
  · exact abs_prefixMean_le _ (by omega) f 1 (fun n _ => hf n)

lemma prefixMean_grid_eventual_upper (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1)
    (a : ℕ) (ha : 0<a) (c : ℝ)
    (h : ∀ᶠ N : ℕ in atTop, |prefixMean (a*N) f|≤c) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, |prefixMean N f|≤c+ε := by
  have hg := (Nat.tendsto_div_const_atTop ha.ne').eventually h
  have ht := tendsto_const_div_atTop_nhds_zero_nat (2*(a : ℝ))
  filter_upwards [hg,eventually_ge_atTop a,ht.eventually_lt_const hε] with N hN hNa he
  have hd : 0<N/a := Nat.div_pos hNa ha
  have hM : 0<a*(N/a) := Nat.mul_pos ha hd
  have hMN : a*(N/a)≤N := Nat.mul_div_le N a
  have hrem : N-a*(N/a)<a := by
    have hr := Nat.mod_lt N ha
    have heq := Nat.div_add_mod N a
    omega
  have hbnd := prefixMean_endpoint_bound (a*(N/a)) N hM hMN f 1 (fun n _ => hf n)
  have herr : |prefixMean N f-prefixMean (a*(N/a)) f|≤2*(a : ℝ)/N := by
    apply hbnd.trans
    simp only [mul_one]
    gcongr
  have htri := abs_sub_le (prefixMean N f) (prefixMean (a*(N/a)) f) 0
  simp only [sub_zero] at htri
  linarith

/-- Cancellation on a single short-ratio harmonic window bounds the limsup of
ordinary mean magnitudes by the relative width. No convergence of the full
harmonic series is required. -/
theorem prefixMean_limsup_le_of_harmonic_window (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1)
    (a b : ℕ) (hb : 0<b) (hba : b<a)
    (hw : Tendsto (fun N => rawHarmonicSum f (a*N)-rawHarmonicSum f (b*N)) atTop (𝓝 0)) :
    limsup (fun N => |prefixMean N f|) atTop ≤ ((a : ℝ)-b)/b := by
  have hhi : IsBoundedUnder (· ≤ ·) atTop (fun N => |prefixMean N f|) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (abs_prefixMean_bounded f hf))
  have hlo : IsBoundedUnder (· ≥ ·) atTop (fun N => |prefixMean N f|) :=
    isBoundedUnder_of_eventually_ge (a := (0 : ℝ)) (Eventually.of_forall (fun _ => abs_nonneg _))
  let v := limsup (fun N => |prefixMean N f|) atTop
  have hbr : (0 : ℝ)<b := by exact_mod_cast hb
  have har : (0 : ℝ)<a := by exact_mod_cast hb.trans hba
  have hbar : (b : ℝ)<a := by exact_mod_cast hba
  have hcoef : 0≤(b : ℝ)/a := by positivity
  have hcoef1 : (b : ℝ)/a≤1 := (div_le_one har).mpr hbar.le
  have hv : v ≤ (b : ℝ)/a*v+((a : ℝ)-b)^2/((a : ℝ)*b) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hm := eventually_lt_of_limsup_lt (show v<v+ε/4 by linarith) hhi
    have hmb := (tendsto_atTop_mono (fun N => by nlinarith [hb] : ∀ N : ℕ, N≤b*N) tendsto_id).eventually hm
    have hh := (Metric.tendsto_nhds.mp hw) (ε/4) (by positivity)
    have hg : ∀ᶠ N : ℕ in atTop, |prefixMean (a*N) f| ≤
        (b : ℝ)/a*v+((a : ℝ)-b)^2/((a : ℝ)*b)+ε/2 := by
      filter_upwards [hmb,hh,eventually_gt_atTop (0 : ℕ)] with N hmN hhN hN
      rw [Real.dist_eq,sub_zero] at hhN
      have he := prefixMean_scaled_harmonic_window_bound f hf a b N hb hba.le hN
      have hm' := mul_le_mul_of_nonneg_left hmN.le hcoef
      have hh' := mul_le_mul_of_nonneg_left hhN.le hcoef
      nlinarith
    have hg' := prefixMean_grid_eventual_upper f hf a (hb.trans hba) _ hg (ε/2) (by positivity)
    have hle := limsup_le_of_le hlo.isCoboundedUnder_le hg'
    dsimp [v]
    convert hle using 1
    ring
  have he : (1-(b : ℝ)/a)*v ≤ ((a : ℝ)-b)^2/((a : ℝ)*b) := by linarith
  have hpos : 0 < 1-(b : ℝ)/a := sub_pos.mpr ((div_lt_one har).mpr hbar)
  have he' : v ≤ (((a : ℝ)-b)^2/((a : ℝ)*b))/(1-(b : ℝ)/a) :=
    (le_div_iff₀ hpos).mpr (by rwa [mul_comm])
  change v ≤ _
  apply he'.trans_eq
  have hsub : (a : ℝ)-b≠0 := sub_ne_zero.mpr hbar.ne'
  field_simp

/-- Arbitrarily narrow cancelling multiplicative windows imply ordinary
Cesaro cancellation for a unit-bounded sequence. -/
theorem prefixMean_zero_of_narrow_harmonic_windows (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1)
    (hw : ∀ ε : ℝ, 0<ε → ∃ a b : ℕ, 0<b ∧ b<a ∧ ((a : ℝ)-b)/b<ε ∧
      Tendsto (fun N => rawHarmonicSum f (a*N)-rawHarmonicSum f (b*N)) atTop (𝓝 0)) :
    Tendsto (fun N => prefixMean N f) atTop (𝓝 0) := by
  have hhi : IsBoundedUnder (· ≤ ·) atTop (fun N => |prefixMean N f|) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (abs_prefixMean_bounded f hf))
  have hv : limsup (fun N => |prefixMean N f|) atTop ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨a,b,hb,hba,he,ht⟩ := hw ε hε
    simpa only [zero_add] using (prefixMean_limsup_le_of_harmonic_window f hf a b hb hba ht).trans he.le
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_lt_of_limsup_lt (hv.trans_lt hε) hhi] with N hN
  simpa only [Real.dist_eq,sub_zero] using hN

#print axioms prefixMean_limsup_le_of_harmonic_window
#print axioms prefixMean_zero_of_narrow_harmonic_windows
end Erdos371
