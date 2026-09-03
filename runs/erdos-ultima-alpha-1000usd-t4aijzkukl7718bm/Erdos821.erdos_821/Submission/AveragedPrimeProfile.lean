import Submission.ColoringPrimeProfile
import Submission.LargePrimeProducts

/-!
# Averaging the prime-exponent profile

In the short-cofactor regime, large-factor multiplicity is exactly the
rough-predecessor indicator. Thus the arity deficit of a predecessor product
is exactly its pool's smooth-prime count, not a new arithmetic lower bound.
-/

open Nat Filter
open scoped Classical BigOperators
namespace Erdos821
set_option maxHeartbeats 3000000

lemma upperFactorMass_eq_finsupp (n y : ℕ) :
    upperFactorMass n y = n.factorization.sum (fun q e => if y ≤ q then e else 0) := by
  simp only [upperFactorMass,Finsupp.sum,Nat.support_factorization,Finset.sum_filter]

lemma upperFactorMass_mul (a b y : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    upperFactorMass (a*b) y = upperFactorMass a y+upperFactorMass b y := by
  simp only [upperFactorMass_eq_finsupp,Nat.factorization_mul ha hb]
  exact Finsupp.sum_add_index' (fun q => by simp)
    (fun q u v => by split_ifs <;> simp)

lemma upperFactorMass_prod {ι : Type*} (S : Finset ι) (f : ι → ℕ) (y : ℕ)
    (hf : ∀ i ∈ S, f i ≠ 0) :
    upperFactorMass (∏ i ∈ S, f i) y = ∑ i ∈ S, upperFactorMass (f i) y := by
  induction S using Finset.induction_on with
  | empty => simp [upperFactorMass]
  | @insert i S hi ih =>
    have hi0 := hf i (Finset.mem_insert_self _ _)
    have hS0 : ∀ j ∈ S, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi,upperFactorMass_mul _ _ _ hi0 (Finset.prod_ne_zero_iff.mpr hS0),
      Finset.sum_insert hi,ih hS0]

lemma upperFactorMass_zero_iff (n y : ℕ) (hn : 0 < n) :
    upperFactorMass n y = 0 ↔ n ∈ Nat.smoothNumbers y := by
  have hcard : (largePrimeDivisors y n).card ≤ upperFactorMass n y := by
    calc
      _ = ∑ _q ∈ largePrimeDivisors y n, 1 := by simp
      _ ≤ upperFactorMass n y := by
        apply Finset.sum_le_sum
        intro q hq
        have hmem : q ∈ n.factorization.support := by
          simpa only [Nat.support_factorization] using (Finset.mem_filter.mp hq).1
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hmem)
  constructor
  · intro h
    exact (largePrimeDivisors_card_zero_iff y n hn).mp (by omega)
  · intro hs
    have he : largePrimeDivisors y n = ∅ :=
      Finset.card_eq_zero.mp ((largePrimeDivisors_card_zero_iff y n hn).mpr hs)
    change ∑ q ∈ largePrimeDivisors y n, n.factorization q = 0
    rw [he,Finset.sum_empty]

/-- The version with full prime-power multiplicities, not just distinct labels. -/
lemma smooth_divisor_upperFactorMass_power_le (y n d : ℕ) (hn : 0 < n)
    (hd : d ∈ Nat.smoothNumbers y) (hdvd : d ∣ n) :
    d*y^(upperFactorMass n y) ≤ n := by
  let Q := n.primeFactors.filter (fun q => y ≤ q)
  let A := ∏ q ∈ Q, q^(n.factorization q)
  have hAn : A ∣ n := by
    have h := Finset.prod_dvd_prod_of_subset Q n.primeFactors
      (fun q => q^(n.factorization q)) (Finset.filter_subset _ _)
    have he : (∏ q ∈ n.primeFactors, q^(n.factorization q)) = n := by
      simpa only [Finsupp.prod,Nat.support_factorization] using Nat.factorization_prod_pow_eq_self hn.ne'
    exact he ▸ h
  have hcop : d.Coprime A := by
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
    apply Nat.Coprime.pow_right
    apply (hqp.coprime_iff_not_dvd.mpr ?_).symm
    intro hqd
    have hlt := Nat.mem_smoothNumbers'.mp hd q hqp hqd
    have hge := (Finset.mem_filter.mp hq).2
    omega
  have hlow : y^(upperFactorMass n y) ≤ A := by
    rw [upperFactorMass,← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod' (fun q hq =>
      Nat.pow_le_pow_left (Finset.mem_filter.mp hq).2 _)
  exact (Nat.mul_le_mul_left d hlow).trans
    (Nat.le_of_dvd hn (hcop.mul_dvd_of_dvd_of_dvd hdvd hAn))

lemma upperFactorMass_lt_of_smooth_divisor (y n d k : ℕ) (hy : 1 ≤ y)
    (hn : 0 < n) (hd : d ∈ Nat.smoothNumbers y) (hdvd : d ∣ n)
    (hsize : n < d*y^k) : upperFactorMass n y < k := by
  by_contra h
  have hpow := Nat.pow_le_pow_right (by omega : 0 < y) (Nat.le_of_not_gt h)
  have hlo := smooth_divisor_upperFactorMass_power_le y n d hn hd hdvd
  have hh := Nat.mul_le_mul_left d hpow
  omega

/-- In the short-cofactor regime, a rough predecessor has one large prime
occurrence, including multiplicity. -/
lemma upperFactorMass_eq_rough_indicator (y n : ℕ) (hy : 1 ≤ y) (hn : 0 < n)
    (hcore : ∃ d : ℕ, d ∈ Nat.smoothNumbers y ∧ d ∣ n ∧ n < d*y^2) :
    upperFactorMass n y = if n ∈ Nat.smoothNumbers y then 0 else 1 := by
  obtain ⟨d,hd,hdvd,hsize⟩ := hcore
  have hlt := upperFactorMass_lt_of_smooth_divisor y n d 2 hy hn hd hdvd hsize
  by_cases hs : n ∈ Nat.smoothNumbers y
  · rw [if_pos hs]
    exact (upperFactorMass_zero_iff n y hn).mpr hs
  · rw [if_neg hs]
    have hne : upperFactorMass n y ≠ 0 := fun h => hs ((upperFactorMass_zero_iff n y hn).mp h)
    omega

/-- The averaged profile is precisely the count of rough predecessors. -/
theorem predecessorProduct_upperFactorMass_eq_rough_card (P : Finset ℕ) (y : ℕ)
    (hy : 1 ≤ y) (hP : ∀ p ∈ P, p.Prime)
    (hcore : ∀ p ∈ P, ∃ d : ℕ,
      d ∈ Nat.smoothNumbers y ∧ d ∣ p-1 ∧ p-1 < d*y^2) :
    upperFactorMass (∏ p ∈ P, (p-1)) y =
      (P.filter (fun p => p-1 ∉ Nat.smoothNumbers y)).card := by
  rw [upperFactorMass_prod P (fun p => p-1) y (fun p hp =>
    (Nat.sub_pos_of_lt (hP p hp).one_lt).ne')]
  simp_rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  rw [upperFactorMass_eq_rough_indicator y (p-1) hy
    (Nat.sub_pos_of_lt (hP p hp).one_lt) (hcore p hp)]
  split_ifs <;> simp_all

/-- Consequently an averaged arity deficit is exactly the supplied smooth
prime count in this regime. No positivity of that count is asserted here. -/
theorem predecessorProduct_arity_deficit_eq_smooth_card (P : Finset ℕ) (y : ℕ)
    (hy : 1 ≤ y) (hP : ∀ p ∈ P, p.Prime)
    (hcore : ∀ p ∈ P, ∃ d : ℕ,
      d ∈ Nat.smoothNumbers y ∧ d ∣ p-1 ∧ p-1 < d*y^2) :
    P.card-upperFactorMass (∏ p ∈ P, (p-1)) y =
      (P.filter (fun p => p-1 ∈ Nat.smoothNumbers y)).card := by
  rw [predecessorProduct_upperFactorMass_eq_rough_card P y hy hP hcore]
  have h := Finset.card_filter_add_card_filter_not
    (s := P) (p := fun p => p-1 ∈ Nat.smoothNumbers y)
  omega

/-- Application to the existing structured families, whenever their cofactor
has room for at most one large prime occurrence. This is still an identity. -/
theorem structuredPredecessor_arity_deficit_eq_smooth_card
    (r t b m : ℕ) (hb : 2 ≤ b) (hm : 2 ≤ m) (ht : t ≤ r+2*b) :
    let P := structuredWitnessPrimes r m
      (AnalyticSieve.progressionScaleN (t*m))
    P.card-upperFactorMass (∏ p ∈ P, (p-1)) (2^(64*b*m)) =
      (P.filter (fun p => p-1 ∈ Nat.smoothNumbers (2^(64*b*m)))).card := by
  dsimp only
  apply predecessorProduct_arity_deficit_eq_smooth_card _ _ (Nat.one_le_pow _ _ (by decide))
    (fun p hp => (structuredWitnessPrimes_has_divisor hp).1)
  intro p hp
  obtain ⟨hpprime,hpN,d,hd,hdvd⟩ := structuredWitnessPrimes_has_divisor hp
  have hprops := primeProductModuli_properties hd
  refine ⟨d,?_,hdvd,?_⟩
  · apply Nat.smoothNumbers_mono _ (primeProductModuli_smooth hm hd)
    exact Nat.pow_le_pow_right (by decide) (by nlinarith)
  · have heq : (AnalyticSieve.progressionScaleN m)^r*(2^(64*b*m))^2 =
        2^(64*(r+2*b)*m) := by
      simp only [AnalyticSieve.progressionScaleN,← pow_mul,← pow_add]
      congr 1
      ring
    calc
      p-1 < AnalyticSieve.progressionScaleN (t*m) := by have := hpprime.two_le; omega
      _ ≤ 2^(64*(r+2*b)*m) := Nat.pow_le_pow_right (by decide) (by
        nlinarith only [Nat.mul_le_mul_right (64*m) ht])
      _ = (AnalyticSieve.progressionScaleN m)^r*(2^(64*b*m))^2 := heq.symm
      _ ≤ d*(2^(64*b*m))^2 := Nat.mul_le_mul_right _ hprops.2.2.2.1

end Erdos821
