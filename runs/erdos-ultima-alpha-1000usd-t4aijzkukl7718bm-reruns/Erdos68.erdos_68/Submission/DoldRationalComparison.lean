import Submission.IndexDependentTelescoping
import Submission.FactorialTailCriterion

/-!
A comparison construction, not the coefficient sequence of Erdős 68.
Prime-power Dold congruences do not by themselves exclude rational sums.
-/
namespace DoldRationalComparison

open Finset Filter
open scoped Topology

lemma missing_divisor_prime_power (p r m d : ℕ) (hp : p.Prime)
    (hd : d ∣ p^(r+1)*m) (hmiss : ¬d ∣ p^r*m) : p^(r+1) ∣ d := by
  induction r generalizing d with
  | zero =>
    simp only [Nat.zero_add, Nat.pow_zero, Nat.pow_one, one_mul] at *
    by_contra hpd
    have hc := ((hp.coprime_iff_not_dvd).mpr hpd).symm
    exact hmiss (hc.dvd_of_dvd_mul_left hd)
  | succ r ih =>
    have hpd : p ∣ d := by
      by_contra hpd
      have hc := ((hp.coprime_iff_not_dvd).mpr hpd).symm
      apply hmiss
      apply hc.dvd_of_dvd_mul_left
      simpa only [pow_succ', mul_assoc] using hd
    obtain ⟨e, rfl⟩ := hpd
    have he : e ∣ p^(r+1)*m := by
      apply (Nat.mul_dvd_mul_iff_left hp.pos).mp
      simpa only [pow_succ', mul_assoc] using hd
    have hem : ¬e ∣ p^r*m := by
      intro hem
      apply hmiss
      simpa only [pow_succ', mul_assoc] using Nat.mul_dvd_mul_left p hem
    simpa only [pow_succ'] using Nat.mul_dvd_mul_left p (ih e he hem)

def divisorTransform (b : ℕ → ℤ) (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (d:ℤ)*b d

lemma divisorTransform_dold (b : ℕ → ℤ) (p r m : ℕ) (hp : p.Prime) (hm : 0 < m) :
    Int.ModEq ((p:ℤ)^(r+1))
      (divisorTransform b (p^(r+1)*m)) (divisorTransform b (p^r*m)) := by
  have hp0 := hp.pos
  have hn : 0 < p^r*m := by positivity
  have hN : 0 < p^(r+1)*m := by positivity
  have hsub : (p^r*m).divisors ⊆ (p^(r+1)*m).divisors := by
    intro d hd
    apply Nat.mem_divisors.mpr
    refine ⟨(Nat.dvd_of_mem_divisors hd).trans ?_, hN.ne'⟩
    rw [pow_succ', mul_assoc]
    exact dvd_mul_left _ _
  unfold divisorTransform
  rw [← Finset.sum_sdiff hsub]
  apply Int.modEq_iff_dvd.mpr
  have hs : (p:ℤ)^(r+1) ∣
      ∑ d ∈ (p^(r+1)*m).divisors \ (p^r*m).divisors, (d:ℤ)*b d := by
    apply Finset.dvd_sum
    intro d hd
    obtain ⟨hd, hmiss⟩ := Finset.mem_sdiff.mp hd
    have hm' : ¬d ∣ p^r*m := fun hh => hmiss (Nat.mem_divisors.mpr ⟨hh, hn.ne'⟩)
    have h := missing_divisor_prime_power p r m d hp (Nat.dvd_of_mem_divisors hd) hm'
    have hi : (p:ℤ)^(r+1) ∣ (d:ℤ) := by exact_mod_cast h
    exact hi.mul_right _
  convert (dvd_neg.mpr hs) using 1
  ring

/-- The first component is an integral tail; the second is an integral
primitive-orbit coefficient. The latter is not required to be nonnegative. -/
def state (n : ℕ) : ℤ × ℤ :=
  if _hn : n ≤ 1 then (2, if n=1 then 1 else 0)
  else
    let t := (state (n-1)).1
    let R := ∑ d : n.properDivisors, (d.val:ℤ)*(state d.val).2
    if n.Prime then ((n:ℤ)*t-1, (n-1).factorial)
    else
      let v := (n:ℤ)*t+n.factorial-R-2
      (2+v % n, v / n)
termination_by n
decreasing_by
  · omega
  · exact (Nat.mem_properDivisors.mp d.property).2

def tail (n : ℕ) : ℤ := (state n).1

def primitive (n : ℕ) : ℤ := (state n).2

def fullCoeff (n : ℕ) : ℤ := divisorTransform primitive n

def coeff (n : ℕ) : ℤ := if n < 2 then 0 else fullCoeff n-n.factorial

lemma state_one : state 1 = (2,1) := by rw [state]; norm_num
lemma tail_one : tail 1 = 2 := by simp [tail, state_one]
lemma primitive_one : primitive 1 = 1 := by simp [primitive, state_one]

lemma prime_state (n : ℕ) (hp : n.Prime) :
    state n = ((n:ℤ)*tail (n-1)-1, ((n-1).factorial:ℤ)) := by
  rw [state, dif_neg (by have := hp.two_le; omega), if_pos hp]
  rfl

lemma composite_state (n : ℕ) (hn : 2 ≤ n) (hp : ¬n.Prime) :
    let R := ∑ d ∈ n.properDivisors, (d:ℤ)*primitive d
    let v := (n:ℤ)*tail (n-1)+n.factorial-R-2
    state n = (2+v % n, v/n) := by
  rw [state, dif_neg (by omega), if_neg hp]
  simp only [tail, primitive]
  rw [Finset.sum_coe_sort n.properDivisors (fun d => (d:ℤ)*(state d).2)]


lemma prime_tail (n : ℕ) (hp : n.Prime) :
    tail n = (n:ℤ)*tail (n-1)-1 := by
  simp only [tail, prime_state n hp]

lemma composite_tail_bounds (n : ℕ) (hn : 2 ≤ n) (hp : ¬n.Prime) :
    2 ≤ tail n ∧ tail n ≤ (n:ℤ)+1 := by
  have hn0 : (0:ℤ) < n := by omega
  have he := congrArg Prod.fst (composite_state n hn hp)
  change tail n = 2+_ at he
  rw [he]
  have hlo := Int.emod_nonneg ((n:ℤ)*tail (n-1)+n.factorial-
    (∑ d ∈ n.properDivisors, (d:ℤ)*primitive d)-2) hn0.ne'
  have hhi := Int.emod_lt_of_pos ((n:ℤ)*tail (n-1)+n.factorial-
    (∑ d ∈ n.properDivisors, (d:ℤ)*primitive d)-2) hn0
  omega

lemma tail_lower (n : ℕ) (hn : 1 ≤ n) : 2 ≤ tail n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n=1
    · subst n; rw [tail_one]
    have hn2 : 2 ≤ n := by omega
    by_cases hp : n.Prime
    · rw [prime_tail n hp]
      have ht := ih (n-1) (by omega) (by omega)
      have hnZ : (2:ℤ) ≤ n := by omega
      nlinarith
    · exact (composite_tail_bounds n hn2 hp).1

lemma tail_two : tail 2 = 3 := by
  rw [prime_tail 2 (by decide)]; norm_num [tail_one]

lemma tail_three : tail 3 = 8 := by
  rw [prime_tail 3 (by decide)]; norm_num [tail_two]

lemma tail_upper (n : ℕ) (hn : 2 ≤ n) : tail n ≤ (n:ℤ)^2 := by
  by_cases hp : n.Prime
  · by_cases h2 : n=2
    · subst n; norm_num [tail_two]
    by_cases h3 : n=3
    · subst n; norm_num [tail_three]
    have hn5 : 5 ≤ n := by
      have ho := hp.eq_two_or_odd
      omega
    have hprev : ¬(n-1).Prime := by
      intro hprev
      have hodd := hp.eq_two_or_odd
      have hodd' := hprev.eq_two_or_odd
      omega
    have ht := (composite_tail_bounds (n-1) (by omega) hprev).2
    rw [prime_tail n hp]
    have hnZ : (5:ℤ) ≤ n := by omega
    rw [Nat.cast_sub (by omega : 1 ≤ n)] at ht
    norm_num only [Nat.cast_one] at ht
    nlinarith
  · have ht := (composite_tail_bounds n hn hp).2
    have hnZ : (2:ℤ) ≤ n := by omega
    nlinarith

lemma fullCoeff_split (n : ℕ) (hn : 0 < n) :
    fullCoeff n = (n:ℤ)*primitive n + ∑ d ∈ n.properDivisors, (d:ℤ)*primitive d := by
  unfold fullCoeff divisorTransform
  rw [← Nat.insert_self_properDivisors hn.ne', Finset.sum_insert Nat.self_notMem_properDivisors]

lemma prime_fullCoeff (n : ℕ) (hp : n.Prime) : fullCoeff n = 1+n.factorial := by
  rw [fullCoeff_split n hp.pos, hp.properDivisors]
  simp only [Finset.sum_singleton, Nat.cast_one, one_mul, primitive_one]
  have hb : primitive n = ((n-1).factorial:ℤ) := by
    simp only [primitive, prime_state n hp]
  rw [hb, ← Nat.cast_mul, Nat.mul_factorial_pred hp.ne_zero]
  ring

lemma coeff_prime (n : ℕ) (hp : n.Prime) : coeff n = 1 := by
  rw [coeff, if_neg (by have := hp.two_le; omega), prime_fullCoeff n hp]
  omega

lemma coeff_recurrence (n : ℕ) (hn : 2 ≤ n) :
    coeff n = (n:ℤ)*tail (n-1)-tail n := by
  by_cases hp : n.Prime
  · rw [coeff_prime n hp, prime_tail n hp]; ring
  · let R := ∑ d ∈ n.properDivisors, (d:ℤ)*primitive d
    let v := (n:ℤ)*tail (n-1)+n.factorial-R-2
    have ht : tail n = 2+v%n := congrArg Prod.fst (composite_state n hn hp)
    have hb : primitive n = v/n := congrArg Prod.snd (composite_state n hn hp)
    rw [coeff, if_neg (by omega), fullCoeff_split n (by omega), hb, ht]
    have he := Int.emod_add_mul_ediv v (n:ℤ)
    change v%n + (n:ℤ)*(v/n) = (n:ℤ)*tail (n-1)+n.factorial-R-2 at he
    change (n:ℤ)*(v/n)+R-n.factorial = (n:ℤ)*tail (n-1)-(2+v%n)
    linarith

lemma coeff_pos (n : ℕ) (hn : 2 ≤ n) : 0 < coeff n := by
  by_cases hp : n.Prime
  · rw [coeff_prime n hp]; omega
  · rw [coeff_recurrence n hn]
    have ht := tail_lower (n-1) (by omega)
    have htu := (composite_tail_bounds n hn hp).2
    have hnZ : (2:ℤ) ≤ n := by omega
    nlinarith

lemma coeff_nonneg (n : ℕ) : 0 ≤ coeff n := by
  by_cases hn : n < 2
  · simp [coeff, hn]
  · exact (coeff_pos n (by omega)).le

lemma fullCoeff_eq (n : ℕ) (hn : 1 ≤ n) : fullCoeff n = coeff n+n.factorial := by
  by_cases hn1 : n=1
  · subst n
    simp [fullCoeff, divisorTransform, primitive_one, coeff]
  · simp [coeff, show ¬n<2 by omega]

/-- These are the same prime-power congruences as for the original Lambert
coefficients, including the smaller singleton factorial correction. -/
lemma coeff_dold (p r m : ℕ) (hp : p.Prime) (hm : 0 < m) :
    Int.ModEq ((p:ℤ)^(r+1)) (coeff (p^(r+1)*m))
      (coeff (p^r*m)+(p^r*m).factorial) := by
  have hp0 := hp.pos
  have hN : 0 < p^(r+1)*m := by positivity
  have h := divisorTransform_dold primitive p r m hp hm
  change Int.ModEq _ (fullCoeff _) (fullCoeff _) at h
  rw [fullCoeff_eq _ hN, fullCoeff_eq _ (show 0 < p^r*m by positivity)] at h
  have hd : p^(r+1) ∣ (p^(r+1)*m).factorial :=
    (dvd_mul_right (p^(r+1)) m).trans (Nat.dvd_factorial hN (le_refl _))
  have hi : (p:ℤ)^(r+1) ∣ ((p^(r+1)*m).factorial:ℤ) := by exact_mod_cast hd
  have he : Int.ModEq ((p:ℤ)^(r+1))
      (coeff (p^(r+1)*m)+(p^(r+1)*m).factorial) (coeff (p^(r+1)*m)) := by
    apply Int.modEq_iff_dvd.mpr
    simpa using dvd_neg.mpr hi
  exact he.symm.trans h

noncomputable def normalizedTail (n : ℕ) : ℝ := (tail n:ℝ)/n.factorial

lemma summable_normalizedTail : Summable normalizedTail := by
  apply (IndexDependentTelescoping.summable_nat_pow_div_factorial 2).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 2] with n hn
  have ht0 : (0:ℝ) ≤ tail n := by exact_mod_cast (tail_lower n (by omega)).trans' (by norm_num)
  have htu : (tail n:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast tail_upper n hn
  dsimp only [normalizedTail]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg ht0 (by positivity))]
  exact div_le_div_of_nonneg_right htu (by positivity)

lemma coeff_div_succ (n : ℕ) (hn : 1 ≤ n) :
    (coeff (n+1):ℝ)/(n+1).factorial = normalizedTail n-normalizedTail (n+1) := by
  rw [coeff_recurrence (n+1) (by omega)]
  simp only [Nat.add_sub_cancel, normalizedTail, Nat.factorial_succ]
  push_cast
  field_simp

lemma hasSum_shifted_coeff :
    HasSum (fun n : ℕ => (coeff (n+2):ℝ)/(n+2).factorial) 2 := by
  have hs1 : Summable (fun n => normalizedTail (n+1)) :=
    (summable_nat_add_iff 1).mpr summable_normalizedTail
  have hs2 : Summable (fun n => normalizedTail (n+2)) :=
    (summable_nat_add_iff 2).mpr summable_normalizedTail
  have he := hs1.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, zero_add, Nat.add_assoc] at he
  have hb : normalizedTail 1 = 2 := by norm_num [normalizedTail, tail_one]
  rw [hb] at he
  have he' : (∑' n, normalizedTail (n+1))-(∑' n, normalizedTail (n+2)) = 2 := by linarith
  have hh := hs1.hasSum.sub hs2.hasSum
  rw [he'] at hh
  convert hh using 1
  funext n
  simpa only [Nat.add_assoc] using coeff_div_succ (n+1) (by omega)

lemma summable_coeff : Summable (fun n : ℕ => (coeff n:ℝ)/n.factorial) :=
  (summable_nat_add_iff 2).mp hasSum_shifted_coeff.summable

/-- This different series has rational sum two. It is not the series in
Spec.lean and does not disprove its conjecture. -/
theorem sum_coeff : (∑' n : ℕ, (coeff n:ℝ)/n.factorial) = 2 := by
  have he := summable_coeff.sum_add_tsum_nat_add 2
  have hz : (∑ n ∈ Finset.range 2, (coeff n:ℝ)/n.factorial) = 0 := by
    norm_num [Finset.sum_range_succ, coeff]
  rw [hz, zero_add, hasSum_shifted_coeff.tsum_eq] at he
  exact he.symm

lemma prefix_identity (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (n+1), (coeff k:ℝ)/k.factorial) = 2-normalizedTail n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Finset.sum_range_succ, coeff, normalizedTail, tail_one]
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih, coeff_div_succ n hn]
    ring

lemma scaledTail_eq (n : ℕ) (hn : 1 ≤ n) :
    FactorialTailCriterion.scaledTail coeff n = (tail n:ℝ) := by
  unfold FactorialTailCriterion.scaledTail
  rw [sum_coeff, prefix_identity n hn]
  simp only [sub_sub_cancel, normalizedTail]
  exact mul_div_cancel₀ _ (by positivity)

#print axioms divisorTransform_dold
#print axioms coeff_dold
#print axioms sum_coeff
#print axioms scaledTail_eq


end DoldRationalComparison
