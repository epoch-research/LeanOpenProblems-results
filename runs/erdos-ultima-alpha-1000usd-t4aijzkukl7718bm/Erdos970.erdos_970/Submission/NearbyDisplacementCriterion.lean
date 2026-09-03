import Submission.CompletionFullPeriod
import Submission.LogLossSquareCubicReduction

/-! A local displacement criterion for ternary void decay. The two blocks
are disjoint, and their separation lies between m and 2m. No bound on the
local covariance sum is assumed implicitly. -/
namespace Erdos970.GapAverages
open Finset Real Filter OneHitLogConcavity Resampling
set_option maxHeartbeats 2200000

noncomputable def nearbyCovarianceSum (P : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ d ∈ range m, coverageCovariance P (range m)
    ((range m).image (fun x => (m+d)+x))

lemma void_antitone_length (P : Finset ℕ) : Antitone (coveredFraction P) := by
  intro m n hmn
  rw [void_eq_population,void_eq_population]
  exact populationCoveredFraction_antitone_population P _ _ (range_mono hmn)

lemma nearby_population_subset (m d : ℕ) (hd : d < m) :
    range m ∪ (range m).image (fun x => (m+d)+x) ⊆ range (3*m) := by
  intro x hx
  rcases mem_union.mp hx with hx | hx
  · have := mem_range.mp hx
    exact mem_range.mpr (by omega)
  · obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    have := mem_range.mp hy
    exact mem_range.mpr (by omega)

/-- Only nearby, disjoint block pairs enter this exact comparison. -/
theorem void_triple_le_nearby_covariance (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    (m : ℝ)*coveredFraction P (3*m) ≤
      (m : ℝ)*coveredFraction P m^2+nearbyCovarianceSum P m := by
  have hh := sum_le_sum (s := range m) (fun d hd =>
    populationCoveredFraction_antitone_population P _ _
      (nearby_population_subset m d (mem_range.mp hd)))
  have he (d : ℕ) : populationCoveredFraction
      (range m ∪ (range m).image (fun x => (m+d)+x)) P =
      coverageCovariance P (range m) ((range m).image (fun x => (m+d)+x))+
        coveredFraction P m^2 := by
    unfold coverageCovariance
    rw [populationCoveredFraction_image_add P (range m) hP,void_eq_population]
    ring
  simp only [sum_const,card_range,nsmul_eq_mul] at hh
  simp_rw [he] at hh
  rw [sum_add_distrib] at hh
  simp only [sum_const,card_range,nsmul_eq_mul] at hh
  simpa only [void_eq_population,nearbyCovarianceSum,add_comm] using hh

/-- A sufficiently small local covariance sum gives a multiplicative
ternary comparison, without asserting adjacent-block independence. -/
theorem void_triple_of_nearby_covariance (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (hm : 0 < m) (a : ℝ)
    (hcov : nearbyCovarianceSum P m ≤
      (m : ℝ)*(a-1)*coveredFraction P m^2) :
    coveredFraction P (3*m) ≤ a*coveredFraction P m^2 := by
  have hh := void_triple_le_nearby_covariance P hP m
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply (mul_le_mul_iff_right₀ hmR).mp
  nlinarith only [hh,hcov]

lemma ternary_square_iteration (f : ℕ → ℝ) (k : ℕ)
    (hf : ∀ n, 0 ≤ f n)
    (hstep : ∀ n, k ≤ n → f (3*n) ≤ f n^2) (j : ℕ) :
    f (3^j*k) ≤ f k^(2^j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hn : k ≤ 3^j*k := Nat.le_mul_of_pos_left k (by positivity)
    have hh := (hstep (3^j*k) hn).trans (pow_le_pow_left₀ (hf _) ih 2)
    convert hh using 1 <;> simp only [← pow_mul,pow_succ] <;> ring

/-- This exact iteration retains the factor-three length change. -/
theorem ternary_scaled_tail (P : Finset ℕ) (m j : ℕ) (a E : ℝ)
    (ha : 1 ≤ a)
    (hstep : ∀ n, m ≤ n → coveredFraction P (3*n) ≤ a*coveredFraction P n^2)
    (hbase : a*coveredFraction P m ≤ exp (-E)) :
    coveredFraction P (3^j*m) ≤ exp (-E*(2 : ℝ)^j) := by
  let f := fun n => a*coveredFraction P n
  have ha0 : 0 ≤ a := by linarith only [ha]
  have hf : ∀ n, 0 ≤ f n := fun n => mul_nonneg ha0 (void_nonneg P n)
  have hs : ∀ n, m ≤ n → f (3*n) ≤ f n^2 := by
    intro n hn
    have hh := mul_le_mul_of_nonneg_left (hstep n hn) ha0
    convert hh using 1 <;> dsimp only [f] <;> ring
  have hi := ternary_square_iteration f m hf hs j
  have hb := pow_le_pow_left₀ (hf _) hbase (2^j)
  have hv := mul_le_mul_of_nonneg_right ha (void_nonneg P (3^j*m))
  simp only [one_mul] at hv
  apply (hv.trans (hi.trans hb)).trans_eq
  rw [← exp_nat_mul]
  congr 1
  push_cast
  ring

/-- An explicitly unproved local correlation premise. The offset is m+d
with d<m; arbitrary distant translates are not included. -/
def LogLossNearbyCovarianceBound (C : ℝ) (B : ℕ) : Prop :=
  ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ,
    (∀ p ∈ P, p.Prime) → P.card ≤ k → ∀ m : ℕ, k ≤ m →
      nearbyCovarianceSum P m ≤
        (m : ℝ)*(exp (C*(k : ℝ)/log (k : ℝ)^B)-1)*coveredFraction P m^2

#print axioms void_triple_le_nearby_covariance
#print axioms ternary_scaled_tail
end Erdos970.GapAverages
