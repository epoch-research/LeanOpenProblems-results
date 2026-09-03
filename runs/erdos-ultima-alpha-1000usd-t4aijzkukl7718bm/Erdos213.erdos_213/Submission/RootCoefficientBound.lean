import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

/-! A coefficient bound for generic root-product identities. This is a
normalization theorem for a restricted construction, not Erdős 213. -/
namespace Erdos213.RootCoefficientBound
noncomputable section
open Polynomial
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

/-- A signed nonnegative power of two, with a bound on its exponent. -/
def SignedPowerTwo (d : ℕ) (q : ℚ) : Prop :=
  ∃ k : ℕ, k ≤ d ∧ (q = 2^k ∨ q = -(2^k))

lemma SignedPowerTwo.ne_zero {d : ℕ} {q : ℚ} (h : SignedPowerTwo d q) : q ≠ 0 := by
  obtain ⟨k,_,hk⟩ := h
  rcases hk with rfl | rfl <;> simp

lemma SignedPowerTwo.mul {m n : ℕ} {a b : ℚ}
    (ha : SignedPowerTwo m a) (hb : SignedPowerTwo n b) :
    SignedPowerTwo (m+n) (a*b) := by
  obtain ⟨i,hi,hai⟩ := ha
  obtain ⟨j,hj,hbj⟩ := hb
  refine ⟨i+j,Nat.add_le_add hi hj,?_⟩
  rcases hai with hai | hai <;> rcases hbj with hbj | hbj
  · left; rw [hai,hbj,pow_add]
  · right; rw [hai,hbj,pow_add]; ring
  · right; rw [hai,hbj,pow_add]; ring
  · left; rw [hai,hbj,pow_add]; ring

/-- A symmetric bounded dyadic ratio, expressed without division. -/
def RatioBound (d : ℕ) (a b : ℚ) : Prop :=
  ∃ i ≤ d, ∃ j ≤ d, a*2^i=b*2^j ∨ a*2^i=-(b*2^j)

/-- Clearing a normalized degree-d dyadic ratio needs at most 2^d. -/
lemma normalized_dyadic_window {d : ℕ} {b : ℚ}
    (h : RatioBound d 1 b) : SignedPowerTwo (2*d) ((2 : ℚ)^d*b) := by
  obtain ⟨i,hi,j,hj,he⟩ := h
  let k := d+i-j
  have hji : j ≤ d+i := by omega
  have hk : k ≤ 2*d := by dsimp [k]; omega
  have hp : (2 : ℚ)^k*2^j=(2 : ℚ)^d*2^i := by
    rw [← pow_add]
    dsimp [k]
    rw [Nat.sub_add_cancel hji,pow_add]
  refine ⟨k,hk,?_⟩
  have hn : (2 : ℚ)^j ≠ 0 := by positivity
  rcases he with he | he
  · left
    apply mul_right_cancel₀ hn
    linear_combination -(2 : ℚ)^d * he - hp
  · right
    apply mul_right_cancel₀ hn
    linear_combination (2 : ℚ)^d * he + hp

lemma RatioBound.refl (d : ℕ) (a : ℚ) : RatioBound d a a :=
  ⟨0,Nat.zero_le _,0,Nat.zero_le _,Or.inl rfl⟩

/-- A dyadic ratio of absolute value at least one has no denominator. -/
lemma RatioBound.signedPowerTwo_of_abs_le {d : ℕ} {a b : ℚ}
    (h : RatioBound d a b) (ha : a ≠ 0) (hab : |a| ≤ |b|) :
    SignedPowerTwo d (b/a) := by
  obtain ⟨i,hi,j,hj,he⟩ := h
  have hpi : 0 < (2 : ℚ)^i := by positivity
  have hpj : 0 < (2 : ℚ)^j := by positivity
  have haa : 0 < |a| := abs_pos.mpr ha
  have habs : |a| *(2 : ℚ)^i=|b| *(2 : ℚ)^j := by
    rcases he with he | he
    · simpa only [abs_mul,abs_pow,abs_of_pos (by norm_num : (0 : ℚ)<2)]
        using congrArg abs he
    · simpa only [abs_mul,abs_pow,abs_neg,abs_of_pos (by norm_num : (0 : ℚ)<2)]
        using congrArg abs he
  have hpow : (2 : ℚ)^j ≤ (2 : ℚ)^i := by nlinarith
  have hji : j ≤ i := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℚ)<2)).mp hpow
  have hp : (2 : ℚ)^(i-j)*2^j=2^i := by rw [← pow_add,Nat.sub_add_cancel hji]
  refine ⟨i-j,by omega,?_⟩
  rcases he with he | he
  · left
    apply (div_eq_iff ha).mpr
    apply mul_right_cancel₀ (ne_of_gt hpj)
    linear_combination -he-a*hp
  · right
    apply (div_eq_iff ha).mpr
    apply mul_right_cancel₀ (ne_of_gt hpj)
    linear_combination he+a*hp

/-- One common rational scale normalizes a finite coefficient family to
signed powers 2^k with 0 ≤ k ≤ d. The minimum is taken only over the given
nonzero family, not over any geometric parameter space. -/
theorem finite_family_normalization {ι : Type*} (S : Finset ι) (hne : S.Nonempty)
    (a : ι → ℚ) {d : ℕ} (ha : ∀ i∈S, a i ≠ 0)
    (hr : ∀ i∈S, ∀ j∈S, i ≠ j → RatioBound d (a i) (a j)) :
    ∃ k∈S, a k ≠ 0 ∧ ∀ i∈S, SignedPowerTwo d (a i/a k) := by
  classical
  obtain ⟨k,hk,hmin⟩ := S.exists_min_image (fun i => |a i|) hne
  refine ⟨k,hk,ha k hk,?_⟩
  intro i hi
  have hh : RatioBound d (a k) (a i) := by
    by_cases he : k=i
    · subst i; exact RatioBound.refl d (a k)
    · exact hr k hk i hi he
  exact hh.signedPowerTwo_of_abs_le (ha k hk) (hmin i hi)

lemma ratio_of_signed_powers {d : ℕ} {a b p q : ℚ}
    (hp : SignedPowerTwo d p) (hq : SignedPowerTwo d q) (he : a*p=b*q) :
    RatioBound d a b := by
  obtain ⟨i,hi,hpi⟩ := hp
  obtain ⟨j,hj,hqj⟩ := hq
  refine ⟨i,hi,j,hj,?_⟩
  rcases hpi with hp | hp <;> rcases hqj with hq | hq
  · left; simpa only [hp,hq] using he
  · right; simpa only [hp,hq,mul_neg] using he
  · right; rw [hp,hq,mul_neg] at he; linarith only [he]
  · left; rw [hp,hq,mul_neg,mul_neg] at he; linarith only [he]

/-- If the right-hand side vanishes to higher order, the first two
nonzero terms on the left must cancel. -/
lemma trailing_relation {R : Type*} [CommRing R] [IsDomain R]
    {p q r : R[X]} {a b c : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (he : C a*p-C b*q=C c*r)
    (hd : p.natTrailingDegree < r.natTrailingDegree) :
    p.natTrailingDegree=q.natTrailingDegree ∧ a*p.trailingCoeff=b*q.trailingCoeff := by
  have hcoeff (n : ℕ) : a*p.coeff n-b*q.coeff n=c*r.coeff n := by
    simpa only [coeff_sub,coeff_C_mul] using congrArg (fun s : R[X] => s.coeff n) he
  have hp' : p.trailingCoeff ≠ 0 := trailingCoeff_nonzero_iff_nonzero.mpr hp
  have hq' : q.trailingCoeff ≠ 0 := trailingCoeff_nonzero_iff_nonzero.mpr hq
  have hdeg : p.natTrailingDegree=q.natTrailingDegree := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hlt
    · have hh := hcoeff p.natTrailingDegree
      rw [coeff_eq_zero_of_lt_natTrailingDegree hlt,
        coeff_eq_zero_of_lt_natTrailingDegree hd,mul_zero,mul_zero,sub_zero] at hh
      exact mul_ne_zero ha hp' hh
    · have hh := hcoeff q.natTrailingDegree
      rw [coeff_eq_zero_of_lt_natTrailingDegree hlt,
        coeff_eq_zero_of_lt_natTrailingDegree (hlt.trans hd),mul_zero,mul_zero,
        zero_sub,neg_eq_zero] at hh
      exact mul_ne_zero hb hq' hh
  refine ⟨hdeg,?_⟩
  have hh := hcoeff p.natTrailingDegree
  rw [coeff_eq_zero_of_lt_natTrailingDegree hd,mul_zero] at hh
  have hh' : a*p.trailingCoeff-b*q.trailingCoeff=0 := by
    simpa only [trailingCoeff,← hdeg] using hh
  exact sub_eq_zero.mp hh'

abbrev B := ℚ[X]
abbrev T := B[X]

def product {ι : Type*} (L : ι → T) (s : Multiset ι) : T := (s.map L).prod

lemma product_zero {ι : Type*} (L : ι → T) : product L 0=1 := by simp [product]
lemma product_cons {ι : Type*} (L : ι → T) (i : ι) (s : Multiset ι) :
    product L (i ::ₘ s)=L i*product L s := by simp [product]

lemma product_signed_power {ι : Type*} (L : ι → T)
    (h : ∀ i, SignedPowerTwo 1 (L i).trailingCoeff.leadingCoeff) (s : Multiset ι) :
    SignedPowerTwo s.card (product L s).trailingCoeff.leadingCoeff := by
  induction s using Multiset.induction_on with
  | empty =>
    refine ⟨0,le_rfl,Or.inl ?_⟩
    simp [product,trailingCoeff]
  | cons i s ih =>
    rw [product_cons,trailingCoeff_mul,leadingCoeff_mul]
    simpa only [Multiset.card_cons,Nat.add_comm] using (h i).mul ih

lemma product_ne_zero {ι : Type*} (L : ι → T)
    (h : ∀ i, SignedPowerTwo 1 (L i).trailingCoeff.leadingCoeff) (s : Multiset ι) :
    product L s ≠ 0 := by
  intro hz
  have hh := (product_signed_power L h s).ne_zero
  simp only [hz,trailingCoeff_zero,leadingCoeff_zero,ne_eq,not_true_eq_false] at hh

lemma product_order {ι : Type*} [DecidableEq ι] (L : ι → T) (k : ι)
    (h : ∀ i, SignedPowerTwo 1 (L i).trailingCoeff.leadingCoeff)
    (ho : ∀ i, (L i).natTrailingDegree=if i=k then 1 else 0) (s : Multiset ι) :
    (product L s).natTrailingDegree=s.count k := by
  induction s using Multiset.induction_on with
  | empty => simp [product]
  | cons i s ih =>
    have hi : L i ≠ 0 := by
      intro he
      have hh := (h i).ne_zero
      simp [he] at hh
    rw [product_cons,natTrailingDegree_mul hi (product_ne_zero L h s),ho,ih]
    by_cases he : i=k
    · subst i; simp [Nat.add_comm]
    · simp [he,Ne.symm he]

lemma exists_larger_count {ι : Type*} [DecidableEq ι] {s u : Multiset ι}
    (hc : s.card=u.card) (hne : s ≠ u) : ∃ k, s.count k < u.count k := by
  by_contra! h
  have hle : u ≤ s := Multiset.le_iff_count.mpr h
  exact hne (Multiset.eq_of_le_of_card_le hle (by omega)).symm

/-- Specializations with a separate order for each factor recover its multiset,
even in the presence of a nonzero constant coefficient. -/
lemma multiset_eq_of_specializations {ι : Type*} [DecidableEq ι]
    (L : ι → ι → T)
    (hpow : ∀ k i, SignedPowerTwo 1 (L k i).trailingCoeff.leadingCoeff)
    (hord : ∀ k i, (L k i).natTrailingDegree=if i=k then 1 else 0)
    {s t : Multiset ι} {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (he : ∀ k, C (C a)*product (L k) s=C (C b)*product (L k) t) : s=t := by
  apply Multiset.ext.mpr
  intro k
  have hca : (C (C a) : T) ≠ 0 := by simpa using ha
  have hcb : (C (C b) : T) ≠ 0 := by simpa using hb
  have hh := congrArg natTrailingDegree (he k)
  simpa only [natTrailingDegree_mul hca (product_ne_zero (L k) (hpow k) s),
    natTrailingDegree_mul hcb (product_ne_zero (L k) (hpow k) t),
    natTrailingDegree_C,zero_add,product_order (L k) k (hpow k) (hord k)] using hh

/-- Abstract specialization form of the coefficient-ratio theorem. -/
theorem ratio_bound_of_specializations {ι : Type*} [DecidableEq ι]
    (L : ι → ι → T)
    (hpow : ∀ k i, SignedPowerTwo 1 (L k i).trailingCoeff.leadingCoeff)
    (hord : ∀ k i, (L k i).natTrailingDegree=if i=k then 1 else 0)
    {s t u : Multiset ι} {d : ℕ}
    (hs : s.card=d) (ht : t.card=d) (hu : u.card=d) (hsu : s ≠ u)
    {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (he : ∀ k, C (C a)*product (L k) s-C (C b)*product (L k) t=
      C (C c)*product (L k) u) : RatioBound d a b := by
  obtain ⟨k,hk⟩ := exists_larger_count (hs.trans hu.symm) hsu
  have hd : (product (L k) s).natTrailingDegree < (product (L k) u).natTrailingDegree := by
    simpa only [product_order (L k) k (hpow k) (hord k)] using hk
  have hh := (trailing_relation (by simpa using ha) (by simpa using hb)
    (product_ne_zero (L k) (hpow k) s) (product_ne_zero (L k) (hpow k) t) (he k) hd).2
  have hl := congrArg leadingCoeff hh
  simp only [leadingCoeff_mul,leadingCoeff_C] at hl
  apply ratio_of_signed_powers ?_ ?_ hl
  · simpa only [hs] using product_signed_power (L k) (hpow k) s
  · simpa only [ht] using product_signed_power (L k) (hpow k) t

/-- Distinct input directions suffice: the additive identity itself prevents
the output direction from coinciding with either input. -/
theorem ratio_bound_of_distinct_specializations {ι : Type*} [DecidableEq ι]
    (L : ι → ι → T)
    (hpow : ∀ k i, SignedPowerTwo 1 (L k i).trailingCoeff.leadingCoeff)
    (hord : ∀ k i, (L k i).natTrailingDegree=if i=k then 1 else 0)
    {s t u : Multiset ι} {d : ℕ}
    (hs : s.card=d) (ht : t.card=d) (hu : u.card=d) (hst : s ≠ t)
    {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (he : ∀ k, C (C a)*product (L k) s-C (C b)*product (L k) t=
      C (C c)*product (L k) u) : RatioBound d a b := by
  apply ratio_bound_of_specializations L hpow hord hs ht hu ?_ ha hb he
  intro hsu
  subst u
  obtain ⟨k,_⟩ := exists_larger_count (hs.trans ht.symm) hst
  have he' (l : ι) : C (C (a-c))*product (L l) s=C (C b)*product (L l) t := by
    simp only [map_sub]
    linear_combination he l
  have hac : a-c ≠ 0 := by
    intro hz
    have hh := he' k
    rw [hz,map_zero,map_zero,zero_mul] at hh
    exact mul_ne_zero (by simpa using hb) (product_ne_zero (L k) (hpow k) t) hh.symm
  exact hst (multiset_eq_of_specializations L hpow hord hac hb he')

#print axioms ratio_bound_of_distinct_specializations
#print axioms finite_family_normalization
#print axioms normalized_dyadic_window
#print axioms trailing_relation
#print axioms ratio_bound_of_specializations
end
end Erdos213.RootCoefficientBound
