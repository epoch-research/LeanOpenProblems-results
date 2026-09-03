import Submission.CofactorPrimeSieve

/-! Finite bounds for comparable large prime factors of adjacent integers.
No density or comparison symmetry is concluded here. -/

namespace Erdos371
namespace FiniteSieve
open Finset

def comparableCofactorPrimeSet (N C X z : ℕ) : Finset ℕ :=
  (Icc 1 X).biUnion fun a => (Icc 1 X).biUnion fun b =>
    if a ≤ C*b ∧ b ≤ C*a then cofactorPrimePairSet N a b z else ∅

lemma mem_comparableCofactorPrimeSet {N C X z n : ℕ} :
    n ∈ comparableCofactorPrimeSet N C X z ↔
      ∃ a ∈ Icc 1 X, ∃ b ∈ Icc 1 X,
        a ≤ C*b ∧ b ≤ C*a ∧ n ∈ cofactorPrimePairSet N a b z := by
  simp only [comparableCofactorPrimeSet, mem_biUnion]
  constructor
  · rintro ⟨a,ha,b,hb,hn⟩
    by_cases hc : a ≤ C*b ∧ b ≤ C*a
    · rw [if_pos hc] at hn
      exact ⟨a,ha,b,hb,hc.1,hc.2,hn⟩
    · simp only [if_neg hc, notMem_empty] at hn
  · rintro ⟨a,ha,b,hb,hab,hba,hn⟩
    exact ⟨a,ha,b,hb,by simpa only [if_pos (show a ≤ C*b ∧ b ≤ C*a from ⟨hab,hba⟩)] using hn⟩

lemma comparableCofactorPrimeSet_card_le (N C X z : ℕ) :
    (comparableCofactorPrimeSet N C X z).card ≤
      ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        if a ≤ C*b ∧ b ≤ C*a then (cofactorPrimePairSet N a b z).card else 0 := by
  unfold comparableCofactorPrimeSet
  refine card_biUnion_le.trans (sum_le_sum fun a ha => ?_)
  refine card_biUnion_le.trans_eq ?_
  apply sum_congr rfl
  intro b hb
  split_ifs <;> simp

/-- The aggregate upper sieve bound for comparable cofactors of size at
most `X`, provided `X² ≤ N`. -/
theorem comparableCofactorPrimeSet_bound (N C X z : ℕ) (hz : 1 ≤ z) (hXN : X^2 ≤ N) :
    ((comparableCofactorPrimeSet N C X z).card : ℝ) ≤
      (4*Real.exp 2*N/(Real.log (z+1 : ℝ))^2) *
        ((C : ℝ)^2 * Real.exp 16 * (1+Real.log X)) +
      (X : ℝ)^2 * ((2*brunDegree z+1 : ℕ) * (z : ℝ)^(4*brunDegree z)) := by
  let K : ℝ := 4*Real.exp 2*N/(Real.log (z+1 : ℝ))^2
  let E : ℝ := (2*brunDegree z+1 : ℕ) * (z : ℝ)^(4*brunDegree z)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hcount : ((comparableCofactorPrimeSet N C X z).card : ℝ) ≤
      ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        if a ≤ C*b ∧ b ≤ C*a then ((cofactorPrimePairSet N a b z).card : ℝ) else 0 := by
    exact_mod_cast comparableCofactorPrimeSet_card_le N C X z
  have hsum : (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      if a ≤ C*b ∧ b ≤ C*a then ((cofactorPrimePairSet N a b z).card : ℝ) else 0) ≤
        K*comparableSlopeSum C X + (X : ℝ)^2*E := by
    calc
      _ ≤ ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
          (K*(if a ≤ C*b ∧ b ≤ C*a then slopeSieveFactor (a*b)/((a : ℝ)*b) else 0)+E) := by
        apply sum_le_sum
        intro a ha
        apply sum_le_sum
        intro b hb
        split_ifs with hcomp
        · exact cofactorPrimePairSet_bound_of_product_le N a b z (mem_Icc.mp ha).1 (mem_Icc.mp hb).1 hz
            ((Nat.mul_le_mul (mem_Icc.mp ha).2 (mem_Icc.mp hb).2).trans (by simpa [sq] using hXN))
        · simpa using hE
      _ = _ := by
        simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
          nsmul_eq_mul, comparableSlopeSum]
        ring
  exact (hcount.trans hsum).trans (add_le_add
    (mul_le_mul_of_nonneg_left (comparableSlopeSum_log_bound C X) hK) le_rfl)

lemma primeCofactor_data (n : ℕ) (hn : 1 < n) :
    0 < primeCofactor n ∧ primeCofactor n ∣ n ∧
      n/primeCofactor n = Nat.maxPrimeFac n := by
  have he := maxPrimeFac_mul_primeCofactor n
  have ha : 0 < primeCofactor n := by
    by_contra h
    have hz : primeCofactor n = 0 := by omega
    rw [hz, mul_zero] at he
    omega
  refine ⟨ha, ⟨Nat.maxPrimeFac n, by nlinarith⟩, ?_⟩
  conv_lhs => lhs; rw [← he]
  exact Nat.mul_div_cancel _ ha

/-- Multiplicatively comparable prime factors give comparable cofactors.
The integrality of the cofactors absorbs the shift by one. -/
lemma comparable_primeCofactors (n C : ℕ) (hn : 1 < n)
    (hpq : Nat.maxPrimeFac n ≤ C*Nat.maxPrimeFac (n+1))
    (hqp : Nat.maxPrimeFac (n+1) ≤ C*Nat.maxPrimeFac n) :
    primeCofactor n ≤ C*primeCofactor (n+1) ∧
      primeCofactor (n+1) ≤ C*primeCofactor n := by
  let p := Nat.maxPrimeFac n
  let q := Nat.maxPrimeFac (n+1)
  let a := primeCofactor n
  let b := primeCofactor (n+1)
  have hp : 2 ≤ p := (Nat.prime_maxPrimeFac_of_one_lt n hn).two_le
  have hq : 2 ≤ q := (Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)).two_le
  have ha : p*a = n := maxPrimeFac_mul_primeCofactor n
  have hb : q*b = n+1 := maxPrimeFac_mul_primeCofactor (n+1)
  change p ≤ C*q at hpq
  change q ≤ C*p at hqp
  change a ≤ C*b ∧ b ≤ C*a
  constructor
  · by_contra h
    have hh : (C*b+1)*p ≤ a*p := Nat.mul_le_mul_right p (by omega)
    have h' := Nat.mul_le_mul_right b hqp
    nlinarith
  · by_contra h
    have hh : (C*a+1)*q ≤ b*q := Nat.mul_le_mul_right q (by omega)
    have h' := Nat.mul_le_mul_right a hpq
    nlinarith

def boundedCofactorNearTieSet (N C X z : ℕ) : Finset ℕ :=
  (Icc 2 N).filter fun n =>
    primeCofactor n ≤ X ∧ primeCofactor (n+1) ≤ X ∧
    Nat.maxPrimeFac n ≤ C*Nat.maxPrimeFac (n+1) ∧
    Nat.maxPrimeFac (n+1) ≤ C*Nat.maxPrimeFac n ∧
    z < Nat.maxPrimeFac n ∧ z < Nat.maxPrimeFac (n+1)

lemma boundedCofactorNearTieSet_subset (N C X z : ℕ) :
    boundedCofactorNearTieSet N C X z ⊆ comparableCofactorPrimeSet N C X z := by
  intro n hn
  obtain ⟨hn, haX, hbX, hpq, hqp, hzp, hzq⟩ := mem_filter.mp hn
  have hn1 : 1 < n := (mem_Icc.mp hn).1
  obtain ⟨ha0, han, hepa⟩ := primeCofactor_data n hn1
  obtain ⟨hb0, hbn, heqb⟩ := primeCofactor_data (n+1) (by omega)
  obtain ⟨hab,hba⟩ := comparable_primeCofactors n C hn1 hpq hqp
  apply mem_comparableCofactorPrimeSet.mpr
  refine ⟨primeCofactor n, mem_Icc.mpr ⟨ha0,haX⟩,
    primeCofactor (n+1), mem_Icc.mpr ⟨hb0,hbX⟩, hab,hba, ?_⟩
  apply mem_filter.mpr
  refine ⟨mem_Icc.mpr ⟨by omega, (mem_Icc.mp hn).2⟩, han,hbn, ?_⟩
  rw [hepa,heqb]
  exact ⟨Nat.prime_maxPrimeFac_of_one_lt n hn1,
    Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega),hzp,hzq⟩

/-- A direct finite bound for the large-prime-factor part of a fixed-ratio
near tie. The subsequent choice of `X` and `z` is not hidden in the statement. -/
theorem boundedCofactorNearTieSet_bound (N C X z : ℕ) (hz : 1 ≤ z) (hXN : X^2 ≤ N) :
    ((boundedCofactorNearTieSet N C X z).card : ℝ) ≤
      (4*Real.exp 2*N/(Real.log (z+1 : ℝ))^2) *
        ((C : ℝ)^2 * Real.exp 16 * (1+Real.log X)) +
      (X : ℝ)^2 * ((2*brunDegree z+1 : ℕ) * (z : ℝ)^(4*brunDegree z)) := by
  exact (Nat.cast_le.mpr (card_le_card (boundedCofactorNearTieSet_subset N C X z))).trans
    (comparableCofactorPrimeSet_bound N C X z hz hXN)

#print axioms boundedCofactorNearTieSet_bound
end FiniteSieve
end Erdos371
