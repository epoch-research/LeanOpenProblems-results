import Submission.SmoothSkewPrimeAveraging

/-! A real Kátai-type criterion for endpoint-dependent bounded sequences with
vanishing fixed-prime dilation defects. This is a single-coordinate
orthogonality tool; no adjacent largest-prime cancellation is asserted. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma sum_Icc_one_eq_shifted_range (g : ℕ → ℝ) (N : ℕ) :
    (∑ m ∈ Icc 1 N, g m) = ∑ n ∈ range N, g (n+1) := by
  simpa only [zero_add,Nat.Ico_zero_eq_range,Ico_add_one_right_eq_Icc] using
    (sum_Ico_add' g 0 N 1).symm

noncomputable def kataiRow (S : Finset ℕ) (a : ℕ → ℝ) (N m : ℕ) : ℝ :=
  ∑ p ∈ S, if m*p ≤ N then a (p*m) else 0

noncomputable def kataiPair (a : ℕ → ℝ) (N p q : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 (N/max p q), a (p*m)*a (q*m)

noncomputable def kataiOffDiagonal (S : Finset ℕ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ S, ∑ q ∈ S, if p=q then 0 else kataiPair a N p q

noncomputable def kataiStableSum (S : Finset ℕ) (f a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ S, ∑ m ∈ Icc 1 (N/p), f m*a (p*m)

noncomputable def kataiDilationError (S : Finset ℕ) (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ S, ∑ m ∈ Icc 1 N, |f (p*m)-f m|

lemma sum_cut_mul (g : ℕ → ℝ) (N p : ℕ) (hp : 0 < p) :
    (∑ m ∈ Icc 1 N, if m*p ≤ N then g m else 0) = ∑ m ∈ Icc 1 (N/p), g m := by
  rw [← sum_filter]
  congr 1
  ext m
  simp only [mem_filter,mem_Icc,← Nat.le_div_iff_mul_le hp]
  have hd : N/p ≤ N := Nat.div_le_self N p
  omega

lemma kataiPair_eq_row_product (a : ℕ → ℝ) (N p q : ℕ) (hp : 0 < p) :
    (∑ m ∈ Icc 1 N,
      (if m*p ≤ N then a (p*m) else 0)*(if m*q ≤ N then a (q*m) else 0)) =
      kataiPair a N p q := by
  have he (m : ℕ) :
      (if m*p ≤ N then a (p*m) else 0)*(if m*q ≤ N then a (q*m) else 0) =
      if m*max p q ≤ N then a (p*m)*a (q*m) else 0 := by
    simp only [mul_max,max_le_iff]
    split_ifs <;> simp_all
  simp_rw [he]
  exact sum_cut_mul _ N (max p q) (hp.trans_le (le_max_left _ _))

lemma kataiStableSum_eq_row (S : Finset ℕ) (f a : ℕ → ℝ) (N : ℕ)
    (hS : ∀ p ∈ S, 0 < p) :
    kataiStableSum S f a N = ∑ m ∈ Icc 1 N, f m*kataiRow S a N m := by
  unfold kataiStableSum kataiRow
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [← sum_cut_mul _ N p (hS p hp)]
  apply sum_congr rfl
  intro m _
  split_ifs <;> simp

lemma kataiStableSum_error (S : Finset ℕ) (f a : ℕ → ℝ) (N : ℕ)
    (hS : ∀ p ∈ S, 0 < p) (ha : ∀ n, |a n| ≤ 1) :
    |primeWeightedSum S (fun n => f n*a n) N-kataiStableSum S f a N| ≤
      kataiDilationError S f N := by
  rw [primeWeightedSum_eq_progressions S _ N hS]
  unfold kataiStableSum kataiDilationError
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro p hp
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ m ∈ Icc 1 (N/p), |f (p*m)-f m| := by
      apply sum_le_sum
      intro m _
      rw [← sub_mul,abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (ha _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (Icc_subset_Icc_right (Nat.div_le_self N p)) (by intros; positivity)

lemma kataiPair_diagonal_bound (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1) (N p : ℕ) :
    kataiPair a N p p ≤ (N : ℝ)/p := by
  unfold kataiPair
  rw [max_self]
  calc
    _ ≤ ∑ _m ∈ Icc 1 (N/p), (1 : ℝ) := by
      apply sum_le_sum
      intro m _
      nlinarith [sq_abs (a (p*m)),ha (p*m),abs_nonneg (a (p*m))]
    _ = (N/p : ℕ) := by simp
    _ ≤ _ := Nat.cast_div_le

lemma kataiRow_energy_bound (S : Finset ℕ) (a : ℕ → ℝ) (N : ℕ)
    (hS : ∀ p ∈ S, 0 < p) (ha : ∀ n, |a n| ≤ 1) :
    (∑ m ∈ Icc 1 N, (kataiRow S a N m)^2) ≤
      N*primeReciprocalSum S+kataiOffDiagonal S a N := by
  have he : (∑ m ∈ Icc 1 N, (kataiRow S a N m)^2) =
      ∑ p ∈ S, ∑ q ∈ S, kataiPair a N p q := by
    simp only [kataiRow,pow_two,sum_mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    exact kataiPair_eq_row_product a N p q (hS p hp)
  rw [he]
  have ht (p q : ℕ) (_hp : p∈S) (_hq : q∈S) : kataiPair a N p q ≤
      (if p=q then (N : ℝ)/p else 0)+(if p=q then 0 else kataiPair a N p q) := by
    by_cases h : p=q
    · subst q; simp only [if_true,add_zero]; exact kataiPair_diagonal_bound a ha N p
    · simp [h]
  have hh := sum_le_sum (fun p hp => sum_le_sum (fun q hq => ht p q hp hq))
  simp only [sum_add_distrib] at hh
  convert hh using 1
  unfold primeReciprocalSum kataiOffDiagonal
  congr 1
  simp [mul_sum,div_eq_mul_inv]

lemma kataiStableSum_sq_bound (S : Finset ℕ) (f a : ℕ → ℝ) (N : ℕ)
    (hS : ∀ p ∈ S, 0 < p) (hf : ∀ n, |f n| ≤ 1) (ha : ∀ n, |a n| ≤ 1) :
    (kataiStableSum S f a N)^2 ≤
      N*(N*primeReciprocalSum S+kataiOffDiagonal S a N) := by
  rw [kataiStableSum_eq_row S f a N hS]
  have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 N) f (kataiRow S a N)
  have hf2 : (∑ m ∈ Icc 1 N, (f m)^2) ≤ N := by
    calc
      _ ≤ ∑ _m ∈ Icc 1 N, (1 : ℝ) := by
        apply sum_le_sum
        intro m _
        nlinarith [sq_abs (f m),hf m,abs_nonneg (f m)]
      _ = _ := by simp
  exact hcs.trans ((mul_le_mul_of_nonneg_right hf2 (by positivity)).trans
    (mul_le_mul_of_nonneg_left (kataiRow_energy_bound S a N hS ha) (Nat.cast_nonneg N)))

lemma kataiOffDiagonal_zero (S : Finset ℕ) (a : ℕ → ℕ → ℝ)
    (hS : ∀ p ∈ S, p.Prime)
    (ha : ∀ p q : ℕ, p.Prime → q.Prime → p≠q →
      Tendsto (fun N => kataiPair (a N) N p q/(N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => kataiOffDiagonal S (a N) N/(N : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_finset_sum S (fun p hp => tendsto_finset_sum S (fun q hq =>
    show Tendsto (fun N => if p=q then (0 : ℝ) else kataiPair (a N) N p q/N) atTop (𝓝 0) from by
      by_cases he : p=q
      · simpa only [if_pos he] using tendsto_const_nhds
      · simpa only [if_neg he] using ha p q (hS p hp) (hS q hq) he))
  simpa only [kataiOffDiagonal,sum_div,ite_div,zero_div,sum_const_zero] using h

lemma kataiDilationError_zero (S : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hS : ∀ p ∈ S, p.Prime)
    (hf : ∀ p : ℕ, p.Prime → Tendsto (fun N =>
      (∑ m ∈ Icc 1 N, |f N (p*m)-f N m|)/(N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => kataiDilationError S (f N) N/(N : ℝ)) atTop (𝓝 0) := by
  simpa only [kataiDilationError,sum_div,sum_const_zero] using
    tendsto_finset_sum S (fun p hp => hf p (hS p hp))

/-- Kátai orthogonality with both the stable sequence and its test permitted
to depend on the natural endpoint. The off-diagonal correlations are actual
shorter progression sums, not averages at a substituted endpoint. -/
theorem stable_katai_orthogonality (f a : ℕ → ℕ → ℝ)
    (hf : ∀ N n, |f N n| ≤ 1) (ha : ∀ N n, |a N n| ≤ 1)
    (hd : ∀ p : ℕ, p.Prime → Tendsto (fun N =>
      (∑ m ∈ Icc 1 N, |f N (p*m)-f N m|)/(N : ℝ)) atTop (𝓝 0))
    (hc : ∀ p q : ℕ, p.Prime → q.Prime → p≠q →
      Tendsto (fun N => kataiPair (a N) N p q/(N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => (∑ n ∈ range N, f N (n+1)*a N (n+1))/(N : ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hs : Tendsto (fun K => Real.sqrt (3/primeHarmonic K)+Real.sqrt (2/primeHarmonic K))
      atTop (𝓝 0) := by
    have h3 := ((tendsto_const_nhds (x := (3 : ℝ))).div_atTop primeHarmonic_atTop).sqrt
    have h2 := ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop primeHarmonic_atTop).sqrt
    simpa using h3.add h2
  obtain ⟨K,hK,hsmall⟩ := ((primeHarmonic_atTop.eventually_gt_atTop (0 : ℝ)).and
    (hs.eventually_lt_const (show (0 : ℝ)<ε/2 by positivity))).exists
  let S := (K+1).primesBelow
  have hS : ∀ p ∈ S, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have hH : 0 < primeReciprocalSum S := hK
  have ho := kataiOffDiagonal_zero S a hS hc
  have he := (kataiDilationError_zero S f hS hd).div_const (primeReciprocalSum S)
  simp only [zero_div] at he
  filter_upwards [eventually_gt_atTop (0 : ℕ),eventually_ge_atTop S.card,
    ho.eventually_le_const hH,he.eventually_lt_const (show (0 : ℝ)<ε/2 by positivity)] with N hN hcard ho he
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hbounded (n : ℕ) : |f N n*a N n| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (hf N n) (abs_nonneg _) (ha N n)
  have ht := primeWeightedSum_error_bound S (fun n => f N n*a N n) N hS hbounded hcard hN hH
  have hE := kataiStableSum_error S (f N) (a N) N (fun p hp => (hS p hp).pos) (ha N)
  have hE' : |primeWeightedSum S (fun n => f N n*a N n) N/(N*primeReciprocalSum S)-
      kataiStableSum S (f N) (a N) N/(N*primeReciprocalSum S)| < ε/2 := by
    rw [← sub_div,abs_div,abs_of_pos (mul_pos hNr hH)]
    exact (div_le_div_of_nonneg_right hE (mul_pos hNr hH).le).trans_lt (by
      simpa only [div_div] using he)
  have hQ : |kataiStableSum S (f N) (a N) N/(N*primeReciprocalSum S)| ≤
      Real.sqrt (2/primeReciprocalSum S) := by
    have hb := kataiStableSum_sq_bound S (f N) (a N) N (fun p hp => (hS p hp).pos) (hf N) (ha N)
    have ho' : kataiOffDiagonal S (a N) N ≤ primeReciprocalSum S*N := (div_le_iff₀ hNr).mp ho
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs,div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos (mul_pos hNr hH))).mpr
    have hid : 2/primeReciprocalSum S*(N*primeReciprocalSum S)^2 =
        2*(N : ℝ)^2*primeReciprocalSum S := by field_simp
    rw [hid]
    nlinarith
  rw [Real.dist_eq,sub_zero]
  have htri := abs_sub_le
    ((∑ n ∈ range N, f N (n+1)*a N (n+1))/(N : ℝ))
    (primeWeightedSum S (fun n => f N n*a N n) N/(N*primeReciprocalSum S)) 0
  have htri2 := abs_sub_le
    (primeWeightedSum S (fun n => f N n*a N n) N/(N*primeReciprocalSum S))
    (kataiStableSum S (f N) (a N) N/(N*primeReciprocalSum S)) 0
  simp only [sub_zero] at htri htri2
  change Real.sqrt (3/primeReciprocalSum S)+Real.sqrt (2/primeReciprocalSum S)<ε/2 at hsmall
  linarith

#print axioms kataiStableSum_sq_bound
#print axioms stable_katai_orthogonality
end Erdos371
