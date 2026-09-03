import Submission.DivisorCovariance

/-! A uniform logarithmic variance bound and finite covariance identities. -/
namespace Erdos972LogarithmicCovariance

open Finset
open Erdos972ExponentialSum Erdos972CommonLogCenter

noncomputable def total (N : ℕ) (f : ℕ → ℝ) := ∑ n ∈ Ioc 0 N, f n
noncomputable def covariance (N : ℕ) (f g : ℕ → ℝ) :=
  total N (fun n => f n*g n)-total N f*total N g/N
noncomputable def logVariance (N : ℕ) := covariance N (fun n => Real.log n) (fun n => Real.log n)

lemma total_abs_le {N : ℕ} {f : ℕ → ℝ} {C : ℝ} (hf : ∀ n ∈ Ioc 0 N, |f n| ≤ C) :
    |total N f| ≤ (N : ℝ)*C := by
  apply (abs_sum_le_sum_abs _ _).trans
  exact (sum_le_sum hf).trans_eq (by simp)

lemma log_sq_le_sqrt {x : ℝ} (hx : 1 ≤ x) : (Real.log x)^2 ≤ 16*Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hroot := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hx0)
  have hh := Real.log_le_sub_one_of_pos hroot
  rw [Real.log_sqrt (Real.sqrt_nonneg x), Real.log_sqrt hx0.le] at hh
  have hlog := Real.log_nonneg hx
  have hs := Real.sq_sqrt (Real.sqrt_nonneg x)
  nlinarith only [hh, hlog, hs, Real.sqrt_nonneg (Real.sqrt x)]

lemma sum_inv_sqrt_le (N : ℕ) : (∑ n ∈ Ioc 0 N, 1/Real.sqrt n) ≤ 2*Real.sqrt N := by
  rw [sum_Ioc_zero_eq_sum_range_succ]
  have hp (n : ℕ) : 1/Real.sqrt (n+1 : ℕ) ≤ 2*(Real.sqrt (n+1 : ℕ)-Real.sqrt n) := by
    have hn1 : (0 : ℝ) < (n+1 : ℕ) := by positivity
    have hs := Real.sqrt_pos.mpr hn1
    apply (div_le_iff₀ hs).mpr
    have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
    have hsq1 := Real.sq_sqrt hn1.le
    have hdiff := sq_nonneg (Real.sqrt (n+1 : ℕ)-Real.sqrt n)
    simp only [Nat.cast_add, Nat.cast_one] at hsq1 hdiff ⊢
    nlinarith only [hsq, hsq1, hdiff]
  calc
    _ ≤ ∑ n ∈ range N, 2*(Real.sqrt (n+1 : ℕ)-Real.sqrt n) := sum_le_sum (fun n _ => hp n)
    _ = _ := by rw [← mul_sum, sum_range_sub (fun n : ℕ => Real.sqrt n)]; simp

lemma endpoint_log_square_sum_le (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (Real.log n-Real.log N)^2) ≤ 32*(N : ℝ) := by
  have hp (n : ℕ) (hn : n ∈ Ioc 0 N) :
      (Real.log n-Real.log N)^2 ≤ 16*Real.sqrt N*(1/Real.sqrt n) := by
    obtain ⟨hn0, hnN⟩ := mem_Ioc.mp hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
    have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr (hn0.trans_le hnN)
    have hratio : (1 : ℝ) ≤ (N : ℝ)/n := (one_le_div hnR).mpr (Nat.cast_le.mpr hnN)
    have hh := log_sq_le_sqrt hratio
    rw [Real.log_div hNR.ne' hnR.ne', Real.sqrt_div hNR.le] at hh
    convert hh using 1 <;> ring
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, 16*Real.sqrt N*(1/Real.sqrt n) := sum_le_sum hp
    _ = 16*Real.sqrt N*(∑ n ∈ Ioc 0 N, 1/Real.sqrt n) := by rw [mul_sum]
    _ ≤ 16*Real.sqrt N*(2*Real.sqrt N) := mul_le_mul_of_nonneg_left (sum_inv_sqrt_le N) (by positivity)
    _ = 32*(N : ℝ) := by rw [show 16*Real.sqrt N*(2*Real.sqrt N) = 32*(Real.sqrt N)^2 by ring, Real.sq_sqrt (Nat.cast_nonneg _)]

lemma sum_square_sub (N : ℕ) (f : ℕ → ℝ) (c : ℝ) :
    (∑ n ∈ Ioc 0 N, (f n-c)^2) = total N (fun n => (f n)^2)-2*c*total N f+(N : ℝ)*c^2 := by
  calc
    _ = ∑ n ∈ Ioc 0 N, ((f n)^2-(2*c)*f n+c^2) := sum_congr rfl (fun n hn => by ring)
    _ = _ := by simp only [total, sum_add_distrib, sum_sub_distrib, ← mul_sum,
      sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]

lemma covariance_self_eq_squares {N : ℕ} (hN : 0 < N) (f : ℕ → ℝ) :
    covariance N f f = ∑ n ∈ Ioc 0 N, (f n-total N f/N)^2 := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [sum_square_sub]
  simp only [covariance, ← pow_two]
  field_simp
  ring

lemma covariance_self_le_center {N : ℕ} (hN : 0 < N) (f : ℕ → ℝ) (c : ℝ) :
    covariance N f f ≤ ∑ n ∈ Ioc 0 N, (f n-c)^2 := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have he : (∑ n ∈ Ioc 0 N, (f n-c)^2)-covariance N f f =
      (total N f-(N : ℝ)*c)^2/N := by
    rw [sum_square_sub]
    simp only [covariance, ← pow_two]
    field_simp
    ring
  have hh : 0 ≤ (total N f-(N : ℝ)*c)^2/N := by positivity
  rw [← he] at hh
  linarith only [hh]

/-- The logarithm has uniformly bounded variance per input, with no PNT or
logarithmic convergence rate involved. -/
theorem logVariance_bounds (N : ℕ) : 0 ≤ logVariance N ∧ logVariance N ≤ 32*(N : ℝ) := by
  by_cases hN : N = 0
  · simp [hN, logVariance, covariance, total]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  refine ⟨?_, (covariance_self_le_center hNpos (fun n => Real.log n) (Real.log N)).trans (endpoint_log_square_sum_le N)⟩
  rw [logVariance, covariance_self_eq_squares hNpos]
  exact sum_nonneg (fun _ _ => sq_nonneg _)

lemma total_affine (N : ℕ) (f : ℕ → ℝ) (a b : ℝ) :
    total N (fun n => a*f n+b) = a*total N f+(N : ℝ)*b := by
  simp only [total, sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]

lemma covariance_affine (N : ℕ) (f : ℕ → ℝ) (a b c d : ℝ) :
    covariance N (fun n => a*f n+b) (fun n => c*f n+d) = a*c*covariance N f f := by
  by_cases hN : N = 0
  · simp [hN, covariance, total]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hp : total N (fun n => (a*f n+b)*(c*f n+d)) =
      a*c*total N (fun n => f n*f n)+(a*d+b*c)*total N f+(N : ℝ)*(b*d) := by
    calc
      _ = total N (fun n => (a*c)*(f n*f n)+(a*d+b*c)*f n+b*d) := by
        apply sum_congr rfl
        intro n hn
        ring
      _ = _ := by simp only [total, sum_add_distrib, ← mul_sum, sum_const,
        Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
        <;> ring
  rw [covariance, hp, total_affine, total_affine]
  unfold covariance
  field_simp
  ring

lemma covariance_affine_log (N : ℕ) (a b c d : ℝ) :
    covariance N (fun n => a*Real.log n+b) (fun n => c*Real.log n+d) = a*c*logVariance N :=
  covariance_affine N (fun n => Real.log n) a b c d

/-- A covariance error can be estimated from two first-moment errors and a
mixed-moment error. Only one actual function and one model need pointwise bounds. -/
lemma covariance_error_bound {N : ℕ} (hN : 0 < N) (f g F G : ℕ → ℝ)
    {Ef Eg Efg A B : ℝ} (hEf : 0 ≤ Ef) (hEg : 0 ≤ Eg)
    (hf : |total N f-total N F| ≤ Ef) (hg : |total N g-total N G| ≤ Eg)
    (hfg : |total N (fun n => f n*g n)-total N (fun n => F n*G n)| ≤ Efg)
    (hF : ∀ n ∈ Ioc 0 N, |F n| ≤ A) (hgb : ∀ n ∈ Ioc 0 N, |g n| ≤ B) :
    |covariance N f g-covariance N F G| ≤ Efg+B*Ef+A*Eg := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hFsum := total_abs_le hF
  have hgsum := total_abs_le hgb
  have he : covariance N f g-covariance N F G =
      (total N (fun n => f n*g n)-total N (fun n => F n*G n))-
        (((total N f-total N F)*total N g+total N F*(total N g-total N G))/N) := by
    unfold covariance
    ring
  have hprod : |((total N f-total N F)*total N g+total N F*(total N g-total N G))/N| ≤ B*Ef+A*Eg := by
    rw [abs_div, abs_of_nonneg hN0.le]
    apply (div_le_iff₀ hN0).mpr
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    have hh₁ := mul_le_mul hf hgsum (abs_nonneg _) hEf
    have hh₂ := mul_le_mul hFsum hg (abs_nonneg _) (by
      have hn : 1 ∈ Ioc 0 N := mem_Ioc.mpr ⟨by omega, hN⟩
      have ha : 0 ≤ A := (abs_nonneg (F 1)).trans (hF 1 hn)
      positivity)
    nlinarith only [hh₁, hh₂]
  rw [he]
  exact (abs_sub _ _).trans (by linarith only [hfg, hprod])

#print axioms logVariance_bounds
#print axioms covariance_error_bound

end Erdos972LogarithmicCovariance
