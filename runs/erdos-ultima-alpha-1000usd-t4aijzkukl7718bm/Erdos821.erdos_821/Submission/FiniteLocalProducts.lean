import Submission.FiniteLocalDenominator
import Submission.TightIntervalTotient

/-!
# Exact finite local-factor cancellation in cofactor averages

The retained Euler factors cancel individually in the main average.
Only the unretained tail remains, and its bound tends to one.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821.Sieve
set_option maxHeartbeats 3000000

noncomputable def finiteLocalBase (Q : Finset ℕ) : ℝ := ∏ q ∈ Q, singularCorrection q

noncomputable def finiteLocalPrimeWeight (Q : Finset ℕ) (p : ℕ) : ℝ :=
  if p ∈ Q then 1/((p : ℝ)-2) else 1/((p : ℝ)-1)

lemma finiteLocalBase_pos (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 2<q) : 0 < finiteLocalBase Q :=
  prod_pos (fun q hq => (singularCorrection_bounds q (hQ q hq)).1)

lemma finiteLocalPrimeWeight_nonneg (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 2<q)
    (p : ℕ) (hp : p.Prime) : 0 ≤ finiteLocalPrimeWeight Q p := by
  unfold finiteLocalPrimeWeight
  split_ifs with hpQ
  · have hh : (2 : ℝ)<p := by exact_mod_cast hQ p hpQ
    exact div_nonneg (by norm_num) (by linarith)
  · have hh : (1 : ℝ)<p := by exact_mod_cast hp.one_lt
    exact div_nonneg (by norm_num) (by linarith)

lemma singularCorrection_factor (q : ℕ) (hq : 2<q) :
    singularCorrection q*(1+1/((q : ℝ)-2)) = 1+1/((q : ℝ)-1) := by
  have hh : (2 : ℝ)<q := by exact_mod_cast hq
  have h1 : (q : ℝ)-1 ≠ 0 := ne_of_gt (by linarith)
  have h2 : (q : ℝ)-2 ≠ 0 := ne_of_gt (by linarith)
  unfold singularCorrection
  field_simp
  ring

lemma singularCorrection_average_factor (q : ℕ) (hq : 2<q) :
    singularCorrection q*(1+(1/((q : ℝ)-2))/(q : ℝ)) = 1 := by
  have hh : (2 : ℝ)<q := by exact_mod_cast hq
  have h0 : (q : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h1 : (q : ℝ)-1 ≠ 0 := ne_of_gt (by linarith)
  have h2 : (q : ℝ)-2 ≠ 0 := ne_of_gt (by linarith)
  unfold singularCorrection
  field_simp
  ring

lemma finiteLocalPrimeWeight_insert_other (Q : Finset ℕ) (q p : ℕ) (hpq : p ≠ q) :
    finiteLocalPrimeWeight (insert q Q) p = finiteLocalPrimeWeight Q p := by
  simp only [finiteLocalPrimeWeight,mem_insert,hpq,false_or]

lemma finiteLocalPrimeWeight_insert_product (Q S : Finset ℕ) (q : ℕ)
    (hqQ : q ∉ Q) (hq : 2<q) :
    singularCorrection q*(∏ p ∈ S, (1+finiteLocalPrimeWeight (insert q Q) p)) =
      (if q ∈ S then 1 else singularCorrection q)*(∏ p ∈ S, (1+finiteLocalPrimeWeight Q p)) := by
  by_cases hqS : q ∈ S
  · rw [if_pos hqS,one_mul,← prod_erase_mul S (fun p => 1+finiteLocalPrimeWeight (insert q Q) p) hqS,
      ← prod_erase_mul S (fun p => 1+finiteLocalPrimeWeight Q p) hqS]
    have he : (∏ p ∈ S.erase q, (1+finiteLocalPrimeWeight (insert q Q) p)) =
        ∏ p ∈ S.erase q, (1+finiteLocalPrimeWeight Q p) := by
      apply prod_congr rfl
      intro p hp
      rw [finiteLocalPrimeWeight_insert_other Q q p (mem_erase.mp hp).1]
    rw [he]
    rw [show finiteLocalPrimeWeight (insert q Q) q=1/((q : ℝ)-2) by simp [finiteLocalPrimeWeight],
      show finiteLocalPrimeWeight Q q=1/((q : ℝ)-1) by simp [finiteLocalPrimeWeight,hqQ]]
    have hh := congrArg (fun x : ℝ => (∏ p ∈ S.erase q, (1+finiteLocalPrimeWeight Q p))*x)
      (singularCorrection_factor q hq)
    convert hh using 1
    ring
  · rw [if_neg hqS]
    congr 1
    apply prod_congr rfl
    intro p hp
    rw [finiteLocalPrimeWeight_insert_other Q q p (by intro he; exact hqS (he ▸ hp))]

lemma finiteLocalPrimeWeight_product (Q S : Finset ℕ) (hQ : ∀ q ∈ Q, 2<q) :
    finiteLocalBase Q*(∏ p ∈ S, (1+finiteLocalPrimeWeight Q p)) =
      (∏ q ∈ Q, if q ∈ S then 1 else singularCorrection q)*
        (∏ p ∈ S, (1+1/((p : ℝ)-1))) := by
  induction Q using Finset.induction_on with
  | empty => simp [finiteLocalBase,finiteLocalPrimeWeight]
  | @insert q Q hqQ ih =>
    have hq := hQ q (mem_insert_self _ _)
    have hh := ih (fun p hp => hQ p (mem_insert_of_mem hp))
    rw [finiteLocalBase,prod_insert hqQ]
    change (singularCorrection q*finiteLocalBase Q)*_ = _
    rw [mul_assoc,mul_comm (finiteLocalBase Q),← mul_assoc,
      finiteLocalPrimeWeight_insert_product Q S q hqQ hq]
    rw [mul_assoc,mul_comm (∏ p ∈ S, (1+finiteLocalPrimeWeight Q p)) (finiteLocalBase Q),hh,prod_insert hqQ]
    ring

lemma finiteLocalPrimeWeight_product_le (Q S : Finset ℕ) (hQ : ∀ q ∈ Q, 2<q)
    (hS : ∀ p ∈ S, p.Prime) :
    finiteLocalBase Q*(∏ p ∈ S, (1+finiteLocalPrimeWeight Q p)) ≤
      ∏ p ∈ S, (1+1/((p : ℝ)-1)) := by
  rw [finiteLocalPrimeWeight_product Q S hQ]
  have hc : (∏ q ∈ Q, if q ∈ S then 1 else singularCorrection q) ≤ 1 := by
    apply prod_le_one
    · intro q hq
      split_ifs
      · norm_num
      · exact (singularCorrection_bounds q (hQ q hq)).1.le
    · intro q hq
      split_ifs
      · rfl
      · exact (singularCorrection_bounds q (hQ q hq)).2
  have hp : 0 ≤ ∏ p ∈ S, (1+1/((p : ℝ)-1)) := by
    apply prod_nonneg
    intro p hp
    have hh : (1 : ℝ)<p := by exact_mod_cast (hS p hp).one_lt
    exact add_nonneg (by norm_num) (div_nonneg (by norm_num) (by linarith))
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hp

lemma finiteLocalCorrection_two_mul (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime ∧ 2<q) (n : ℕ) :
    finiteLocalCorrection Q (2*n) = finiteLocalCorrection Q n := by
  apply finiteLocalCorrection_mul Q 2 n (fun q hq => (hQ q hq).1)
  intro q hq hd
  have hh := Nat.le_of_dvd (by decide : 0<2) hd
  have := (hQ q hq).2
  omega

lemma finite_corrected_reciprocal_totient_double_eq (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2<q) (n : ℕ) (hn : 0<n) :
    finiteLocalCorrection Q (2*n)/((2*n).totient : ℝ) =
      finiteLocalBase Q*(∏ p ∈ n.primeFactors.erase 2, (1+finiteLocalPrimeWeight Q p))/(n : ℝ) := by
  rw [finiteLocalPrimeWeight_product Q _ (fun q hq => (hQ q hq).2),
    finiteLocalCorrection_two_mul Q hQ n]
  have he : (∏ q ∈ Q, if q ∈ n.primeFactors.erase 2 then (1 : ℝ) else singularCorrection q) =
      finiteLocalCorrection Q n := by
    apply prod_congr rfl
    intro q hq
    have hmem : q ∈ n.primeFactors.erase 2 ↔ q ∣ n := by
      constructor
      · exact fun h => Nat.dvd_of_mem_primeFactors (mem_erase.mp h).2
      · intro h
        exact mem_erase.mpr ⟨by have := (hQ q hq).2; omega,(hQ q hq).1.mem_primeFactors h hn.ne'⟩
    simp only [hmem]
  rw [he,div_eq_mul_one_div,reciprocal_totient_double_eq_odd_product n hn]
  ring

/-- When the retained pool is contained in the averaging pool, its local
factors cancel EXACTLY, leaving only the unretained Euler product. -/
lemma finiteLocalPrimeWeight_average_product (Q P : Finset ℕ) (hQ : ∀ q ∈ Q, 2<q) (hQP : Q ⊆ P) :
    finiteLocalBase Q*(∏ p ∈ P, (1+finiteLocalPrimeWeight Q p/(p : ℝ))) =
      ∏ p ∈ P \ Q, (1+1/((p : ℝ)*((p : ℝ)-1))) := by
  rw [← prod_sdiff hQP]
  have he : (∏ p ∈ P \ Q, (1+finiteLocalPrimeWeight Q p/(p : ℝ))) =
      ∏ p ∈ P \ Q, (1+1/((p : ℝ)*((p : ℝ)-1))) := by
    apply prod_congr rfl
    intro p hp
    simp only [finiteLocalPrimeWeight,if_neg (mem_sdiff.mp hp).2,div_div,mul_comm]
  rw [he]
  have hc : finiteLocalBase Q*(∏ p ∈ Q, (1+finiteLocalPrimeWeight Q p/(p : ℝ))) = 1 := by
    unfold finiteLocalBase
    rw [← prod_mul_distrib]
    calc
      _ = ∏ q ∈ Q, (1 : ℝ) := by
        apply prod_congr rfl
        intro q hq
        simp only [finiteLocalPrimeWeight,if_pos hq]
        exact singularCorrection_average_factor q (hQ q hq)
      _ = 1 := prod_const_one
  calc
    _ = (∏ p ∈ P \ Q, (1+1/((p : ℝ)*((p : ℝ)-1))))*
        (finiteLocalBase Q*(∏ p ∈ Q, (1+finiteLocalPrimeWeight Q p/(p : ℝ)))) := by ring
    _ = _ := by rw [hc,mul_one]

end Erdos821.Sieve
