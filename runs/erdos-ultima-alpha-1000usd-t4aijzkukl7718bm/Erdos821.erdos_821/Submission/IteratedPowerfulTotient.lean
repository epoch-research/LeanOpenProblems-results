import Submission.PowerfulTotient
import Submission.IteratedTotientValuation

/-!
# Prime-exponent information retained by fixed totient iterates

This auxiliary file investigates injectivity on inputs whose nonzero prime
exponents are all greater than the iterate count. It does not settle Erdős 821.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821.IteratedTotient

set_option maxHeartbeats 2000000

lemma factorization_totient (m p : ℕ) (hm : m ≠ 0) :
    (Nat.totient m).factorization p = m.factorization p - 1 +
      ∑ q ∈ m.primeFactors, (q-1).factorization p := by
  have hnonzero (q : ℕ) (hq : q ∈ m.primeFactors) :
      q ^ (m.factorization q - 1) * (q-1) ≠ 0 := by
    have hp := Nat.prime_of_mem_primeFactors hq
    exact mul_ne_zero (pow_ne_zero _ hp.ne_zero) (Nat.sub_pos_of_lt hp.one_lt).ne'
  rw [Nat.totient_eq_prod_factorization hm,
    Nat.prod_factorization_eq_prod_primeFactors,
    Nat.factorization_prod_apply hnonzero]
  have hterm (q : ℕ) (hq : q ∈ m.primeFactors) :
      (q ^ (m.factorization q - 1) * (q-1)).factorization p =
        (if q = p then m.factorization p - 1 else 0) + (q-1).factorization p := by
    have hqprime := Nat.prime_of_mem_primeFactors hq
    rw [Nat.factorization_mul (pow_ne_zero _ hqprime.ne_zero)
      (Nat.sub_pos_of_lt hqprime.one_lt).ne', Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.Prime.factorization hqprime]
    by_cases hqp : q = p
    · subst q
      simp
    · simp [hqp]
  simp_rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  congr 1
  by_cases hp : p ∈ m.primeFactors
  · simp [hp]
  · have hz : m.factorization p = 0 := by
      simpa only [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] using hp
    simp [hz]

lemma predecessor_factorization_eq_zero_of_le {q p : ℕ}
    (hq : q.Prime) (hqp : q ≤ p) : (q-1).factorization p = 0 := by
  have hq2 := hq.two_le
  apply Nat.factorization_eq_zero_of_not_dvd
  exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hq.one_lt) (by omega)

lemma predecessor_factorization_sum_high (m p : ℕ) :
    (∑ q ∈ m.primeFactors, (q-1).factorization p) =
      ∑ q ∈ m.primeFactors.filter (fun q => p < q), (q-1).factorization p := by
  apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro q hq hnot
  have hle : q ≤ p := by
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨hq, Nat.lt_of_not_ge h⟩)
  exact predecessor_factorization_eq_zero_of_le (Nat.prime_of_mem_primeFactors hq) hle

lemma high_primeFactors_eq {a b p : ℕ}
    (H : ∀ q : ℕ, p < q → a.factorization q = b.factorization q) :
    a.primeFactors.filter (fun q => p < q) =
      b.primeFactors.filter (fun q => p < q) := by
  ext q
  simp only [Finset.mem_filter, ← Nat.support_factorization, Finsupp.mem_support_iff]
  by_cases hpq : p < q
  · rw [H q hpq]
  · simp [hpq]

lemma predecessor_factorization_sums_eq {a b p : ℕ}
    (H : ∀ q : ℕ, p < q → a.factorization q = b.factorization q) :
    (∑ q ∈ a.primeFactors, (q-1).factorization p) =
      ∑ q ∈ b.primeFactors, (q-1).factorization p := by
  rw [predecessor_factorization_sum_high, predecessor_factorization_sum_high,
    high_primeFactors_eq H]

lemma high_factorization_totient_eq {a b p : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (H : ∀ q : ℕ, p < q → a.factorization q = b.factorization q) :
    ∀ q : ℕ, p < q → (Nat.totient a).factorization q =
      (Nat.totient b).factorization q := by
  intro q hpq
  rw [factorization_totient a q ha, factorization_totient b q hb, H q hpq,
    predecessor_factorization_sums_eq (fun r hqr => H r (hpq.trans hqr))]

/-- If all higher input-prime exponents agree, a collision after k steps
can identify different exponents at p only when both exponents are at most k. -/
lemma factorization_eq_or_le_of_iterate_eq (k : ℕ) {a b p : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (H : ∀ q : ℕ, p < q → a.factorization q = b.factorization q)
    (he : (Nat.totient^[k]) a = (Nat.totient^[k]) b) :
    a.factorization p = b.factorization p ∨
      (a.factorization p ≤ k ∧ b.factorization p ≤ k) := by
  induction k generalizing a b with
  | zero =>
    left
    simpa only [Function.iterate_zero_apply] using congrArg (fun n : ℕ => n.factorization p) he
  | succ k ih =>
    have hφa : Nat.totient a ≠ 0 := (Nat.totient_pos.mpr (Nat.pos_of_ne_zero ha)).ne'
    have hφb : Nat.totient b ≠ 0 := (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hb)).ne'
    have he' : (Nat.totient^[k]) (Nat.totient a) = (Nat.totient^[k]) (Nat.totient b) := by
      simpa only [Function.iterate_succ_apply] using he
    have Hφ := high_factorization_totient_eq ha hb H
    have hsum := predecessor_factorization_sums_eq H
    rcases ih hφa hφb Hφ he' with hsame | hsmall
    · rw [factorization_totient a p ha, factorization_totient b p hb, hsum] at hsame
      omega
    · rw [factorization_totient a p ha, factorization_totient b p hb] at hsmall
      omega

lemma iterate_eq_zero_iff (k m : ℕ) : (Nat.totient^[k]) m = 0 ↔ m = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Nat.totient_eq_zero, ih]

lemma mem_primeFactors_union_of_factorization_ne {a b p : ℕ}
    (hne : a.factorization p ≠ b.factorization p) :
    p ∈ a.primeFactors ∪ b.primeFactors := by
  by_contra hp
  simp only [Finset.mem_union, ← Nat.support_factorization,
    Finsupp.mem_support_iff, not_or, not_not] at hp
  exact hne (hp.1.trans hp.2.symm)

/-- Agreement on all exponents that could be lost in k iterations is enough
for injectivity inside a fixed iterated-totient fiber. -/
theorem eq_of_iterate_eq_of_low_exponent_agreement (k : ℕ) {a b : ℕ}
    (he : (Nat.totient^[k]) a = (Nat.totient^[k]) b)
    (H : ∀ p : ℕ, a.factorization p ≤ k → b.factorization p ≤ k →
      a.factorization p = b.factorization p) : a = b := by
  by_cases hb : b = 0
  · subst b
    exact (iterate_eq_zero_iff k a).mp
      (he.trans ((iterate_eq_zero_iff k 0).mpr rfl))
  have ha : a ≠ 0 := by
    intro ha
    have hz := (iterate_eq_zero_iff k a).mpr ha
    exact hb ((iterate_eq_zero_iff k b).mp (he.symm.trans hz))
  by_contra hab
  have hdiff : ∃ p : ℕ, a.factorization p ≠ b.factorization p := by
    by_contra h
    push_neg at h
    exact hab (Nat.eq_of_factorization_eq ha hb h)
  let S := (a.primeFactors ∪ b.primeFactors).filter
    (fun p => a.factorization p ≠ b.factorization p)
  have hS : S.Nonempty := by
    obtain ⟨p, hp⟩ := hdiff
    exact ⟨p, Finset.mem_filter.mpr ⟨mem_primeFactors_union_of_factorization_ne hp, hp⟩⟩
  let p := S.max' hS
  have hpS : p ∈ S := Finset.max'_mem _ _
  have hp : a.factorization p ≠ b.factorization p := (Finset.mem_filter.mp hpS).2
  have Hhigh : ∀ q : ℕ, p < q → a.factorization q = b.factorization q := by
    intro q hpq
    by_contra hq
    have hqS : q ∈ S :=
      Finset.mem_filter.mpr ⟨mem_primeFactors_union_of_factorization_ne hq, hq⟩
    have hqp : q ≤ p := Finset.le_max' S q hqS
    omega
  rcases factorization_eq_or_le_of_iterate_eq k ha hb Hhigh he with hsame | hsmall
  · exact hp hsame
  · exact hp (H p hsmall.1 hsmall.2)

/-- The part of the input factorization with exponents between 1 and k.
It records both the relevant primes and their exponents. -/
noncomputable def lowExponentSignature (k m : ℕ) : ℕ →₀ ℕ :=
  m.factorization.filter (fun p => m.factorization p ≤ k)

@[simp] lemma lowExponentSignature_apply (k m p : ℕ) :
    lowExponentSignature k m p =
      if m.factorization p ≤ k then m.factorization p else 0 := by
  simp only [lowExponentSignature, Finsupp.filter_apply]

/-- Every iterated fiber is injectively encoded by its low-exponent part.
This does not bound the number of possible low-exponent prime labels. -/
theorem lowExponentSignature_injOn_fiber (k n : ℕ) :
    Set.InjOn (lowExponentSignature k) {m : ℕ | (Nat.totient^[k]) m = n} := by
  intro a ha b hb he
  apply eq_of_iterate_eq_of_low_exponent_agreement k (ha.trans hb.symm)
  intro p hap hbp
  have h := congrArg (fun f : ℕ →₀ ℕ => f p) he
  simpa only [lowExponentSignature_apply, if_pos hap, if_pos hbp] using h

/-- Inputs with no positive prime exponent at most k. For k=1 this is the
usual powerful-input condition. -/
def HighPowerInput (k m : ℕ) : Prop := ∀ p ∈ m.primeFactors, k < m.factorization p

/-- The kth iterate of totient is injective on (k+1)-full inputs. -/
theorem iterate_injective_on_highPower (k : ℕ) :
    Set.InjOn (Nat.totient^[k]) {m : ℕ | HighPowerInput k m} := by
  intro a ha b hb he
  apply eq_of_iterate_eq_of_low_exponent_agreement k he
  intro p hap hbp
  have hap0 : a.factorization p = 0 := by
    by_contra hne
    have hp : p ∈ a.primeFactors := by
      simpa only [← Nat.support_factorization, Finsupp.mem_support_iff] using hne
    exact (not_lt_of_ge hap) (ha p hp)
  have hbp0 : b.factorization p = 0 := by
    by_contra hne
    have hp : p ∈ b.primeFactors := by
      simpa only [← Nat.support_factorization, Finsupp.mem_support_iff] using hne
    exact (not_lt_of_ge hbp) (hb p hp)
  exact hap0.trans hbp0.symm

lemma highPowerInput_pow (k a r : ℕ) (hr : k < r) : HighPowerInput k (a^r) := by
  intro p hp
  have hpos : 0 < (a^r).factorization p := by
    have hne : (a^r).factorization p ≠ 0 := by
      simpa only [← Nat.support_factorization, Finsupp.mem_support_iff] using hp
    exact Nat.pos_of_ne_zero hne
  have he : (a^r).factorization p = r * a.factorization p := by
    simp [Nat.factorization_pow, smul_eq_mul]
  have ha : 0 < a.factorization p := by rw [he] at hpos; nlinarith
  have hle : r ≤ (a^r).factorization p := by
    rw [he]
    exact Nat.le_mul_of_pos_right r ha
  exact hr.trans_le hle

/-- On rth powers, every iterate count k<r is injective. -/
theorem iterate_pow_injective (k r : ℕ) (hr : k < r) :
    Function.Injective (fun a : ℕ => (Nat.totient^[k]) (a^r)) := by
  intro a b he
  apply Nat.pow_left_injective (by omega : r ≠ 0)
  exact iterate_injective_on_highPower k (highPowerInput_pow k a r hr)
    (highPowerInput_pow k b r hr) he

lemma highPower_fiber_card_le_one (k n : ℕ) :
    {m : ℕ | HighPowerInput k m ∧ (Nat.totient^[k]) m = n}.ncard ≤ 1 := by
  apply (Set.ncard_le_one ((finite_fiber k n).subset (fun _ hm => hm.2))).mpr
  intro a ha b hb
  exact iterate_injective_on_highPower k ha.1 hb.1 (ha.2.trans hb.2.symm)

end Erdos821.IteratedTotient
