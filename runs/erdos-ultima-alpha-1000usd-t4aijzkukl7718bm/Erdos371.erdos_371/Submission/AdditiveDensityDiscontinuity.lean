import Submission.Explore

/-! A linear family of completely additive scores for which comparison density
is discontinuous in the parameter. This is not an arithmetic counterexample
to Erdős 371; it rules out transferring comparison density using pointwise
continuity of additive scores alone. -/
namespace Erdos371.AdditiveDensityDiscontinuity
open Filter
open scoped Topology

noncomputable def score (t : ℝ) (n : ℕ) : ℝ :=
  Real.log n-t*(n.factorization 2 : ℝ)

lemma score_mul (t : ℝ) (a b : ℕ) (ha : a≠0) (hb : b≠0) :
    score t (a*b)=score t a+score t b := by
  have haR : (a : ℝ)≠0 := by exact_mod_cast ha
  have hbR : (b : ℝ)≠0 := by exact_mod_cast hb
  simp only [score,Nat.cast_mul,Real.log_mul haR hbR,
    Nat.factorization_mul ha hb,Finsupp.add_apply,Nat.cast_add]
  ring

lemma score_continuous (n : ℕ) : Continuous (fun t : ℝ => score t n) := by
  unfold score
  fun_prop


lemma score_analyticAt (n : ℕ) (t : ℝ) : AnalyticAt ℝ (fun s : ℝ => score s n) t := by
  exact analyticAt_const.sub (analyticAt_id.mul analyticAt_const)

lemma score_tendsto_zero_parameter (n : ℕ) :
    Tendsto (fun t : ℝ => score t n) (nhds 0) (nhds (Real.log n)) := by
  simpa [score] using (score_continuous n).tendsto 0

lemma log_increment_bound (n : ℕ) (hn : 0<n) :
    Real.log (n+1 : ℕ)-Real.log n ≤ 1/(n : ℝ) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ)<(n+1)/n by positivity)
  rw [Real.log_div (by positivity) hnR.ne'] at h
  have he : ((n : ℝ)+1)/n-1=1/n := by field_simp; ring
  rw [he] at h
  simpa only [Nat.cast_add,Nat.cast_one] using h

lemma score_rise_iff_even (t : ℝ) (ht : 0<t) (n : ℕ)
    (hn : 0<n) (hsmall : 1/(n : ℝ)<t) :
    score t n<score t (n+1) ↔ Even n := by
  have hlog := log_increment_bound n hn
  have hpos : Real.log n<Real.log (n+1 : ℕ) :=
    Real.log_lt_log (by exact_mod_cast hn) (by exact_mod_cast Nat.lt_succ_self n)
  by_cases he : Even n
  · have hd : 2 ∣ n := even_iff_two_dvd.mp he
    have hnd : ¬2 ∣ n+1 := by omega
    have hz := Nat.factorization_eq_zero_of_not_dvd hnd
    have hv : 0≤(n.factorization 2 : ℝ) := Nat.cast_nonneg _
    apply iff_of_true ?_ he
    dsimp [score]
    rw [hz,Nat.cast_zero,mul_zero,sub_zero]
    nlinarith
  · have hnd : ¬2 ∣ n := fun h => he (even_iff_two_dvd.mpr h)
    have hd : 2 ∣ n+1 := by omega
    have hz := Nat.factorization_eq_zero_of_not_dvd hnd
    have hv := Nat.prime_two.factorization_pos_of_dvd (by omega : n+1≠0) hd
    have hvR : (1 : ℝ)≤(n+1).factorization 2 := by exact_mod_cast hv
    apply iff_of_false ?_ he
    dsimp [score]
    rw [hz,Nat.cast_zero,mul_zero,sub_zero]
    nlinarith

lemma score_eventually_rise_iff_even (t : ℝ) (ht : 0<t) :
    ∀ᶠ n : ℕ in atTop, score t n<score t (n+1) ↔ Even n := by
  filter_upwards [tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const ht,
    eventually_gt_atTop (0 : ℕ)] with n hs hn
  exact score_rise_iff_even t ht n hn hs

/-- Every positive parameter gives density one half, despite the parameter
zero score being log(n). -/
theorem score_positive_parameter_density_half (t : ℝ) (ht : 0<t) :
    {n : ℕ | score t n<score t (n+1)}.HasDensity (1/2) := by
  classical
  obtain ⟨B,hB⟩ := eventually_atTop.mp (score_eventually_rise_iff_even t ht)
  apply (density_iff_of_exception (fun n => score t n<score t (n+1)) Even
    (fun n => n<B) (fun n hn => hB n (by omega))
    (Nat.hasDensity_zero_of_finite (Set.finite_Iio B)) (1/2)).mpr
  exact Nat.hasDensity_even

/-- At the limiting parameter all positive-index comparisons rise. -/
theorem score_zero_parameter_density_one :
    {n : ℕ | score 0 n<score 0 (n+1)}.HasDensity 1 := by
  classical
  apply (density_iff_of_exception (fun n => score 0 n<score 0 (n+1))
    (fun _ => True) (fun n => n<1) ?_
    (Nat.hasDensity_zero_of_finite (Set.finite_Iio 1)) 1).mpr
  · exact Set.HasDensity.univ
  · intro n hn
    have hn0 : 0<n := by omega
    have h := Real.log_lt_log (by exact_mod_cast hn0 : (0 : ℝ)<n)
      (by exact_mod_cast Nat.lt_succ_self n : (n : ℝ)<(n+1 : ℕ))
    simpa only [score,zero_mul,sub_zero,iff_true] using h

/-- Thus even a linear, pointwise-continuous family of completely additive
functions need not have comparison densities continuous at a parameter. -/
theorem pointwise_continuous_additive_density_jump :
    (∀ t : ℝ, ∀ a b : ℕ, a≠0 → b≠0 → score t (a*b)=score t a+score t b) ∧
    (∀ n : ℕ, Continuous (fun t : ℝ => score t n)) ∧
    (∀ t : ℝ, 0<t → {n : ℕ | score t n<score t (n+1)}.HasDensity (1/2)) ∧
    {n : ℕ | score 0 n<score 0 (n+1)}.HasDensity 1 :=
  ⟨score_mul,score_continuous,score_positive_parameter_density_half,
    score_zero_parameter_density_one⟩

lemma log_increment_lower (n : ℕ) (hn : 0<n) :
    1/(n+1 : ℕ) ≤ Real.log (n+1 : ℕ)-Real.log n := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ)<(n+1)/n by positivity)
  rw [Real.log_div (by positivity) hnR.ne'] at h
  have he : 1-(((n : ℝ)+1)/n)⁻¹=1/(n+1) := by field_simp; ring
  rw [he] at h
  simpa only [Nat.cast_add,Nat.cast_one] using h

noncomputable def diagonalParameter (N : ℕ) : ℝ := 1/(N+1 : ℝ)^3

lemma diagonalParameter_pos (N : ℕ) : 0<diagonalParameter N := by
  unfold diagonalParameter
  positivity

lemma diagonalParameter_tendsto_zero :
    Tendsto diagonalParameter atTop (nhds 0) := by
  have ht : Tendsto (fun N : ℕ => (1 : ℝ)/(N+1 : ℕ)) atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr tendsto_one_div_atTop_nhds_zero_nat
  simpa only [diagonalParameter,Nat.cast_add,Nat.cast_one,div_pow,one_pow,zero_pow,
    ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true] using ht.pow 3

/-- There is no uniform-in-parameter onset of density one half: at this
positive parameter, every positive-index comparison in the prefix rises. -/
theorem diagonalParameter_prefix_rises (N n : ℕ) (hn : 0<n) (hnN : n≤N) :
    score (diagonalParameter N) n<score (diagonalParameter N) (n+1) := by
  have hN1 : 1≤N := hn.trans_le hnN
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ)<N+1 := by positivity
  have hv : ((n+1).factorization 2 : ℝ)≤N+1 := by
    exact_mod_cast (Nat.factorization_lt 2 (by omega : n+1≠0)).le.trans (by omega : n+1≤N+1)
  have hm := mul_le_mul_of_nonneg_left hv (diagonalParameter_pos N).le
  have hsmall : diagonalParameter N*(N+1)<1/(N+1) := by
    unfold diagonalParameter
    apply (lt_div_iff₀ hN0).mpr
    have he : 1/(N+1 : ℝ)^3*(N+1)*(N+1)=1/(N+1) := by field_simp
    rw [he]
    exact (div_lt_one hN0).mpr (by linarith)
  have hinv : (1 : ℝ)/(N+1)≤1/(n+1 : ℕ) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (show n+1≤N+1 by omega)
  have hlog := log_increment_lower n hn
  have hv0 : 0≤diagonalParameter N*(n.factorization 2 : ℝ) := by
    exact mul_nonneg (diagonalParameter_pos N).le (Nat.cast_nonneg _)
  dsimp only [score]
  linarith

/-- The diagonal event has density one even though every fixed positive
parameter has comparison density one half and the parameters tend to zero. -/
theorem diagonal_parameter_density_one :
    {n : ℕ | score (diagonalParameter n) n<score (diagonalParameter n) (n+1)}.HasDensity 1 := by
  classical
  apply (density_iff_of_exception
    (fun n => score (diagonalParameter n) n<score (diagonalParameter n) (n+1))
    (fun _ => True) (fun n => n<1) ?_
    (Nat.hasDensity_zero_of_finite (Set.finite_Iio 1)) 1).mpr
  · exact Set.HasDensity.univ
  · intro n hn
    exact iff_of_true (diagonalParameter_prefix_rises n n (by omega) le_rfl) trivial

#print axioms pointwise_continuous_additive_density_jump
#print axioms score_analyticAt
#print axioms diagonalParameter_prefix_rises
#print axioms diagonal_parameter_density_one
end Erdos371.AdditiveDensityDiscontinuity
