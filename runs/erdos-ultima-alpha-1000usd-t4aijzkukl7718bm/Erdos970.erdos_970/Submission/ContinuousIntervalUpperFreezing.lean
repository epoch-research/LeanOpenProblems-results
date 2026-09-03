import Submission.ContinuousIntervalDilation
import Submission.ContinuousIntervalReference
import Submission.PrimeSetMertens

/-! Fixed-length upper envelopes eventually stop changing. These are lower
bounds for an auxiliary upper envelope, not lower bounds for Jacobsthal's
function, and do not establish quadratic positivity. -/
namespace Erdos970.ContinuousInterval
open Finset Real
set_option maxHeartbeats 800000

lemma envelope_upper_antitone (q : ℕ → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (y : ℝ) :
    Antitone (fun k => (envelope q k y).2) := by
  apply antitone_nat_of_succ_le
  intro k
  change (envelope q k y).2 - (envelope q k ((y+1)*q k-1)).1 ≤ _
  exact sub_le_self _ ((envelope_regular q k (fun i _ => hq i)).lower_nonneg _)

/-- Any zero region large enough to contain every later lower argument
makes the upper branch constant from that point onwards. -/
lemma envelope_upper_freezes (q : ℕ → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (J : ℕ) (y : ℝ)
    (harg : ∀ i, J ≤ i → (y+1)*q i-1 ≤ i) (k : ℕ) (hJk : J ≤ k) :
    (envelope q k y).2 = (envelope q J y).2 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hJk
  induction t with
  | zero => simp
  | succ t ih =>
    change (envelope q (J+t) y).2 -
      (envelope q (J+t) ((y+1)*q (J+t)-1)).1 = _
    rw [lower_zero_of_le_card q (J+t) (fun i _ => hq i) _
      (harg (J+t) (by omega)),sub_zero,ih (by omega)]

/-- The density at a freezing stage supplies a lower source for the upper
branch at every stage, including earlier stages. -/
lemma density_mul_le_upper_of_freezing (q : ℕ → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (J : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (harg : ∀ i, J ≤ i → (y+1)*q i-1 ≤ i) (k : ℕ) :
    density q J*y ≤ (envelope q k y).2 := by
  have hr := envelope_regular q J (fun i _ => hq i)
  have hg := hr.upper_growth 0 y (by norm_num) hy
  rw [hr.upper_zero,sub_zero,sub_zero] at hg
  rcases le_total k J with hkJ | hJk
  · exact hg.trans (envelope_upper_antitone q hq y hkJ)
  · rwa [envelope_upper_freezes q hq J y harg k hJk]

lemma upper_arg_le_card_of_square (q : ℕ → ℝ)
    (hq : ∀ i, q i ≤ 1/((i : ℝ)+2)) (J : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (hyJ : y ≤ (J : ℝ)^2) (i : ℕ) (hJi : J ≤ i) :
    (y+1)*q i-1 ≤ i := by
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hJiR : (J : ℝ) ≤ i := by exact_mod_cast hJi
  have hs : (J : ℝ)^2 ≤ (i : ℝ)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg J) hJiR 2
  have hb : y+1 ≤ ((i : ℝ)+1)*((i : ℝ)+2) := by nlinarith
  have hdiv : (y+1)/((i : ℝ)+2) ≤ (i : ℝ)+1 :=
    (div_le_iff₀ (by positivity)).mpr hb
  have hmul := mul_le_mul_of_nonneg_left (hq i) (by linarith : 0 ≤ y+1)
  rw [mul_one_div] at hmul
  linarith

/-- For marginals no larger than 1/(i+2), the upper envelope at length y
has already frozen once the stage reaches ceil(sqrt(y)). -/
theorem envelope_upper_freezes_sqrt (q : ℕ → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hqi : ∀ i, q i ≤ 1/((i : ℝ)+2))
    (y : ℝ) (hy : 0 ≤ y) (k : ℕ) (hk : ⌈sqrt y⌉₊ ≤ k) :
    (envelope q k y).2 = (envelope q ⌈sqrt y⌉₊ y).2 := by
  apply envelope_upper_freezes q hq _ y _ k hk
  apply upper_arg_le_card_of_square q hqi _ y hy
  have hc := Nat.le_ceil (sqrt y)
  have hs := sq_sqrt hy
  have hn := sqrt_nonneg y
  nlinarith

lemma referenceMarginal_real_bounds (i : ℕ) :
    0 ≤ (referenceMarginal i : ℝ) ∧ (referenceMarginal i : ℝ) ≤ 1 := by
  exact_mod_cast referenceMarginal_bounds i

lemma referenceMarginal_real_le_index (i : ℕ) :
    (referenceMarginal i : ℝ) ≤ 1/((i : ℝ)+2) := by
  simp only [referenceMarginal,Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_two_le_nth_prime i

lemma reference_density_lower (k : ℕ) :
    exp (-WeightedMertens.reciprocalConstant-1)/log ((k : ℝ)+2) ≤
      density (fun i => (referenceMarginal i : ℝ)) k := by
  classical
  let P := (range k).image (Nat.nth Nat.Prime)
  have hinj : Function.Injective (Nat.nth Nat.Prime) :=
    (Nat.nth_strictMono Nat.infinite_setOf_prime).injective
  have hc : P.card ≤ k := by
    exact (card_image_le).trans (by simp)
  have hp : ∀ p ∈ P, p.Prime := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact Nat.prime_nth_prime i
  have hh := WeightedMertens.prime_set_density_lower P hp k hc
  dsimp only [P] at hh
  rw [prod_image hinj.injOn] at hh
  simpa [density,referenceMarginal] using hh

/-- Uniform in the stage k. The argument in the logarithm is of square-root
scale; this is stronger than freezing only after ceil(y). -/
theorem reference_upper_log_source (k : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    exp (-WeightedMertens.reciprocalConstant-1)*y/log (sqrt y+3) ≤
      (envelope (fun i => (referenceMarginal i : ℝ)) k y).2 := by
  have hc := Nat.le_ceil (sqrt y)
  have hs := sq_sqrt hy
  have hn := sqrt_nonneg y
  have hysq : y ≤ (⌈sqrt y⌉₊ : ℝ)^2 := by nlinarith
  have hu := density_mul_le_upper_of_freezing
    (fun i => (referenceMarginal i : ℝ)) referenceMarginal_real_bounds
    ⌈sqrt y⌉₊ y hy
    (upper_arg_le_card_of_square _ referenceMarginal_real_le_index _ y hy hysq) k
  have hd := mul_le_mul_of_nonneg_right (reference_density_lower ⌈sqrt y⌉₊) hy
  have hceil := Nat.ceil_lt_add_one hn
  have hl0 : 0 < log ((⌈sqrt y⌉₊ : ℝ)+2) := log_pos (by have := Nat.cast_nonneg (α := ℝ) ⌈sqrt y⌉₊; linarith)
  have hl : log ((⌈sqrt y⌉₊ : ℝ)+2) ≤ log (sqrt y+3) := by
    apply log_le_log (by positivity)
    linarith
  have he := div_le_div_of_nonneg_left
    (mul_nonneg (exp_pos (-WeightedMertens.reciprocalConstant-1)).le hy) hl0 hl
  apply he.trans
  convert hd.trans hu using 1 <;> ring

#print axioms envelope_upper_freezes_sqrt
#print axioms reference_upper_log_source
end Erdos970.ContinuousInterval
