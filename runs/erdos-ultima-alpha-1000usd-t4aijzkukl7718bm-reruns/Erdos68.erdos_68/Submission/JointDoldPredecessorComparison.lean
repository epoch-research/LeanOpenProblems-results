import Submission.DoldRationalComparison

/-!
A different rational factorial series with both modified Dold and predecessor
congruences. This is not a proof or disproof of the conjecture in Spec.lean.
-/
namespace JointDoldPredecessorComparison
open Finset Filter DoldRationalComparison
open scoped Topology

/-- The first component is an integral tail; the second is an integral
primitive-orbit coefficient. The latter is not required to be nonnegative. -/
def state (n : ℕ) : ℤ × ℤ :=
  if _hn : n ≤ 1 then (4, if n=1 then 1 else 0)
  else
    let t := (state (n-1)).1
    let R := ∑ d : n.properDivisors, (d.val:ℤ)*(state d.val).2
    if n.Prime then ((n:ℤ)*t-1, (n-1).factorial)
    else
      let k : ℤ := 1-R+n.factorial
      let v := (n:ℤ)*t+n.factorial-R-2*n
      let M : ℤ := n*(n-1)
      (2*n+(v-n*k)%M, k+(n-1)*((v-n*k)/M))
termination_by n
decreasing_by
  · omega
  · exact (Nat.mem_properDivisors.mp d.property).2

def tail (n : ℕ) : ℤ := (state n).1

def primitive (n : ℕ) : ℤ := (state n).2

def fullCoeff (n : ℕ) : ℤ := divisorTransform primitive n

def coeff (n : ℕ) : ℤ := if n < 2 then 0 else fullCoeff n-n.factorial

lemma state_one : state 1 = (4,1) := by rw [state]; norm_num
lemma tail_one : tail 1 = 4 := by simp [tail, state_one]
lemma primitive_one : primitive 1 = 1 := by simp [primitive, state_one]

lemma prime_state (n : ℕ) (hp : n.Prime) :
    state n = ((n:ℤ)*tail (n-1)-1, ((n-1).factorial:ℤ)) := by
  rw [state, dif_neg (by have := hp.two_le; omega), if_pos hp]
  rfl

lemma composite_state (n : ℕ) (hn : 2 ≤ n) (hp : ¬n.Prime) :
    let R := ∑ d ∈ n.properDivisors, (d:ℤ)*primitive d
    let k : ℤ := 1-R+n.factorial
    let v := (n:ℤ)*tail (n-1)+n.factorial-R-2*n
    let M : ℤ := n*(n-1)
    state n = (2*n+(v-n*k)%M, k+(n-1)*((v-n*k)/M)) := by
  rw [state, dif_neg (by omega), if_neg hp]
  simp only [tail, primitive]
  rw [Finset.sum_coe_sort n.properDivisors (fun d => (d:ℤ)*(state d).2)]

lemma prime_tail (n : ℕ) (hp : n.Prime) :
    tail n = (n:ℤ)*tail (n-1)-1 := by
  simp only [tail, prime_state n hp]

lemma composite_tail_bounds (n : ℕ) (hn : 2 ≤ n) (hp : ¬n.Prime) :
    2*(n:ℤ) ≤ tail n ∧ tail n < (n:ℤ)^2+n := by
  have hn0 : (0:ℤ) < n*(n-1) := mul_pos (by omega) (by omega)
  have he := congrArg Prod.fst (composite_state n hn hp)
  change tail n = 2*(n:ℤ)+_ at he
  rw [he]
  have hlo := Int.emod_nonneg ((n:ℤ)*tail (n-1)+n.factorial-
    (∑ d ∈ n.properDivisors, (d:ℤ)*primitive d)-2*n-
    n*(1-(∑ d ∈ n.properDivisors, (d:ℤ)*primitive d)+n.factorial)) hn0.ne'
  have hhi := Int.emod_lt_of_pos ((n:ℤ)*tail (n-1)+n.factorial-
    (∑ d ∈ n.properDivisors, (d:ℤ)*primitive d)-2*n-
    n*(1-(∑ d ∈ n.properDivisors, (d:ℤ)*primitive d)+n.factorial)) hn0
  constructor <;> nlinarith

lemma tail_two : tail 2 = 7 := by
  rw [prime_tail 2 (by decide)]; norm_num [tail_one]

lemma tail_three : tail 3 = 20 := by
  rw [prime_tail 3 (by decide)]; norm_num [tail_two]

lemma tail_lower (n : ℕ) (hn : 1 ≤ n) : 2*(n:ℤ) ≤ tail n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n=1
    · subst n; norm_num [tail_one]
    by_cases hn2 : n=2
    · subst n; norm_num [tail_two]
    have hn3 : 3 ≤ n := by omega
    by_cases hp : n.Prime
    · rw [prime_tail n hp]
      have ht := ih (n-1) (by omega) (by omega)
      rw [Nat.cast_sub (by omega : 1 ≤ n)] at ht
      norm_num only [Nat.cast_one] at ht
      have hm := mul_le_mul_of_nonneg_left ht (show (0:ℤ) ≤ n by omega)
      have hh : (0:ℤ) ≤ (n:ℤ)*((n:ℤ)-3) := mul_nonneg (by omega) (by omega)
      nlinarith
    · exact (composite_tail_bounds n (by omega) hp).1

lemma tail_upper (n : ℕ) (hn : 2 ≤ n) : tail n < (n:ℤ)^3 := by
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
    rw [Nat.cast_sub (by omega : 1 ≤ n)] at ht
    norm_num only [Nat.cast_one] at ht
    have hm := mul_lt_mul_of_pos_left ht (show (0:ℤ) < n by omega)
    nlinarith [sq_nonneg (n:ℤ)]
  · have ht := (composite_tail_bounds n hn hp).2
    have hh : (0:ℤ) ≤ (n:ℤ)^2*((n:ℤ)-2) := mul_nonneg (sq_nonneg _) (by omega)
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
    let k : ℤ := 1-R+n.factorial
    let v := (n:ℤ)*tail (n-1)+n.factorial-R-2*n
    let M : ℤ := n*(n-1)
    have ht : tail n = 2*(n:ℤ)+(v-n*k)%M :=
      congrArg Prod.fst (composite_state n hn hp)
    have hb : primitive n = k+((n:ℤ)-1)*((v-n*k)/M) :=
      congrArg Prod.snd (composite_state n hn hp)
    rw [coeff, if_neg (by omega), fullCoeff_split n (by omega), hb, ht]
    have he := Int.emod_add_mul_ediv (v-n*k) M
    dsimp only [M, v, k] at he ⊢
    dsimp only [R] at he
    nlinarith

lemma coeff_pos (n : ℕ) (hn : 2 ≤ n) : 0 < coeff n := by
  by_cases hp : n.Prime
  · rw [coeff_prime n hp]; omega
  · have hn4 : 4 ≤ n := by
      have h2 : n ≠ 2 := by rintro rfl; exact hp (by decide)
      have h3 : n ≠ 3 := by rintro rfl; exact hp (by decide)
      omega
    rw [coeff_recurrence n hn]
    have ht := tail_lower (n-1) (by omega)
    have htu := (composite_tail_bounds n hn hp).2
    rw [Nat.cast_sub (by omega : 1 ≤ n)] at ht
    norm_num only [Nat.cast_one] at ht
    have hm := mul_le_mul_of_nonneg_left ht (show (0:ℤ) ≤ n by omega)
    have hh : (0:ℤ) ≤ (n:ℤ)*((n:ℤ)-3) := mul_nonneg (by omega) (by omega)
    nlinarith

lemma predecessor_congruence (n : ℕ) (hn : 2 ≤ n) :
    ((n:ℤ)-1) ∣ coeff n-1 := by
  by_cases hp : n.Prime
  · rw [coeff_prime n hp]; simp
  · let R := ∑ d ∈ n.properDivisors, (d:ℤ)*primitive d
    let k : ℤ := 1-R+n.factorial
    let v := (n:ℤ)*tail (n-1)+n.factorial-R-2*n
    let M : ℤ := n*(n-1)
    have hb : primitive n = k+((n:ℤ)-1)*((v-n*k)/M) :=
      congrArg Prod.snd (composite_state n hn hp)
    rw [coeff, if_neg (by omega), fullCoeff_split n (by omega), hb]
    refine ⟨k+(n:ℤ)*((v-n*k)/M), ?_⟩
    dsimp only [k, R]
    ring

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
  apply (IndexDependentTelescoping.summable_nat_pow_div_factorial 3).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 2] with n hn
  have ht0 : (0:ℝ) ≤ tail n := by exact_mod_cast (show (0:ℤ) ≤ tail n by have := tail_lower n (by omega); omega)
  have htu : (tail n:ℝ) ≤ (n:ℝ)^3 := by exact_mod_cast (tail_upper n hn).le
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
    HasSum (fun n : ℕ => (coeff (n+2):ℝ)/(n+2).factorial) 4 := by
  have hs1 : Summable (fun n => normalizedTail (n+1)) :=
    (summable_nat_add_iff 1).mpr summable_normalizedTail
  have hs2 : Summable (fun n => normalizedTail (n+2)) :=
    (summable_nat_add_iff 2).mpr summable_normalizedTail
  have he := hs1.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, zero_add, Nat.add_assoc] at he
  have hb : normalizedTail 1 = 4 := by norm_num [normalizedTail, tail_one]
  rw [hb] at he
  have he' : (∑' n, normalizedTail (n+1))-(∑' n, normalizedTail (n+2)) = 4 := by linarith
  have hh := hs1.hasSum.sub hs2.hasSum
  rw [he'] at hh
  convert hh using 1
  funext n
  simpa only [Nat.add_assoc] using coeff_div_succ (n+1) (by omega)

lemma summable_coeff : Summable (fun n : ℕ => (coeff n:ℝ)/n.factorial) :=
  (summable_nat_add_iff 2).mp hasSum_shifted_coeff.summable

/-- This different series has rational sum four. It is not the series in
Spec.lean and does not disprove its conjecture. -/
theorem sum_coeff : (∑' n : ℕ, (coeff n:ℝ)/n.factorial) = 4 := by
  have he := summable_coeff.sum_add_tsum_nat_add 2
  have hz : (∑ n ∈ Finset.range 2, (coeff n:ℝ)/n.factorial) = 0 := by
    norm_num [Finset.sum_range_succ, coeff]
  rw [hz, zero_add, hasSum_shifted_coeff.tsum_eq] at he
  exact he.symm

lemma prefix_identity (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (n+1), (coeff k:ℝ)/k.factorial) = 4-normalizedTail n := by
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

lemma scaledTail_bounds (n : ℕ) (hn : 2 ≤ n) :
    2*(n:ℝ) ≤ FactorialTailCriterion.scaledTail coeff n ∧
      FactorialTailCriterion.scaledTail coeff n < (n:ℝ)^3 := by
  rw [scaledTail_eq n (by omega)]
  constructor
  · exact_mod_cast tail_lower n (by omega)
  · exact_mod_cast tail_upper n hn

lemma coefficient_four : coeff 4 = 67 := by
  have hp2 : primitive 2 = 1 := by
    have h := congrArg Prod.snd (prime_state 2 (by decide))
    norm_num only [Nat.reduceSub, Nat.factorial_one, Nat.cast_one] at h
    exact h
  have h := congrArg Prod.fst (composite_state 4 (by decide) (by decide))
  change tail 4 = _ at h
  have hd : Nat.properDivisors 4 = {1,2} := by decide
  norm_num [hd, primitive_one, hp2, tail_three] at h
  rw [coeff_recurrence 4 (by omega)]
  norm_num [tail_three, h]

/-- Joint congruences still permit a rational sum with cubic scaled tails.
The comparison is not the coefficient sequence of the conjecture. -/
theorem comparison_properties :
    (∀ n : ℕ, 0 ≤ coeff n) ∧
    (∀ n : ℕ, 2 ≤ n → 0 < coeff n) ∧
    (∀ n : ℕ, 2 ≤ n → ((n:ℤ)-1) ∣ coeff n-1) ∧
    (∀ p : ℕ, p.Prime → coeff p = 1) ∧
    (∀ p r m : ℕ, p.Prime → 0 < m →
      Int.ModEq ((p:ℤ)^(r+1)) (coeff (p^(r+1)*m))
        (coeff (p^r*m)+(p^r*m).factorial)) ∧
    (∀ n : ℕ, 2 ≤ n → 2*(n:ℝ) ≤ FactorialTailCriterion.scaledTail coeff n ∧
      FactorialTailCriterion.scaledTail coeff n < (n:ℝ)^3) ∧
    (∑' n : ℕ, (coeff n:ℝ)/n.factorial) = 4 :=
  ⟨coeff_nonneg, coeff_pos, predecessor_congruence, coeff_prime,
    coeff_dold, scaledTail_bounds, sum_coeff⟩

#print axioms comparison_properties
#print axioms coefficient_four
#print axioms predecessor_congruence
#print axioms tail_upper
#print axioms coeff_dold
#print axioms sum_coeff
#print axioms scaledTail_eq


end JointDoldPredecessorComparison
