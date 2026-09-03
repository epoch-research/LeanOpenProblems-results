import Submission.LocalDenominatorComparison

/-!
# Simultaneous retention of finitely many local sieve factors

The finite prime pool is fixed before the sieve length tends to infinity.
Each retained prime incurs only a fixed loss in logarithmic length.
-/
open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.Sieve
set_option maxHeartbeats 3000000

noncomputable def singularCorrection (q : ℕ) : ℝ :=
  (q : ℝ)*((q : ℝ)-2)/((q : ℝ)-1)^2

noncomputable def finiteLocalCorrection (Q : Finset ℕ) (a : ℕ) : ℝ :=
  ∏ q ∈ Q, if q ∣ a then 1 else singularCorrection q

def finiteLocalLength (Q : Finset ℕ) : ℕ := ∑ q ∈ Q, q

lemma singularCorrection_bounds (q : ℕ) (hq : 2<q) :
    0 < singularCorrection q ∧ singularCorrection q ≤ 1 := by
  have hqR : (2 : ℝ)<q := by exact_mod_cast hq
  have hden : 0 < ((q : ℝ)-1)^2 := sq_pos_of_pos (by linarith)
  constructor
  · exact div_pos (mul_pos (by linarith) (by linarith)) hden
  · apply (div_le_one hden).mpr
    nlinarith

lemma finiteLocalCorrection_pos (Q : Finset ℕ) (a : ℕ) (hQ : ∀ q ∈ Q, 2<q) :
    0 < finiteLocalCorrection Q a := by
  apply prod_pos
  intro q hq
  split_ifs
  · norm_num
  · exact (singularCorrection_bounds q (hQ q hq)).1

lemma finiteLocalCorrection_le_one (Q : Finset ℕ) (a : ℕ) (hQ : ∀ q ∈ Q, 2<q) :
    finiteLocalCorrection Q a ≤ 1 := by
  apply prod_le_one
  · intro q hq
    split_ifs
    · norm_num
    · exact (singularCorrection_bounds q (hQ q hq)).1.le
  · intro q hq
    split_ifs
    · rfl
    · exact (singularCorrection_bounds q (hQ q hq)).2

lemma finiteLocalCorrection_mul (Q : Finset ℕ) (d a : ℕ)
    (hQ : ∀ q ∈ Q, q.Prime) (hd : ∀ q ∈ Q, ¬q ∣ d) :
    finiteLocalCorrection Q (d*a) = finiteLocalCorrection Q a := by
  apply prod_congr rfl
  intro q hq
  simp only [(hQ q hq).dvd_mul,hd q hq,false_or]

lemma finiteLocalCorrection_prime_mul (Q : Finset ℕ) (q a : ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hq : q.Prime) (hqQ : q ∉ Q) :
    finiteLocalCorrection Q (q*a) = finiteLocalCorrection Q a := by
  apply finiteLocalCorrection_mul Q q a hQ
  intro p hp hpd
  have he := (Nat.prime_dvd_prime_iff_eq (hQ p hp) hq).mp hpd
  exact hqQ (he ▸ hp)

lemma mixedPairDenominator_local_comparison (a q z Z : ℕ) (P : Finset ℕ)
    (ha : 2 ∣ a) (hq : q.Prime) (hq2 : 2<q) (hqa : ¬q ∣ a)
    (hP : ∀ p ∈ P, p.Prime) (hqP : q ∈ P) (hz : q*z ≤ Z) :
    (((q : ℝ)-1)/((q : ℝ)-2))*mixedPairDenominator (q*a) z P ≤
      mixedPairDenominator a Z P := by
  have hqR : (2 : ℝ)<q := by exact_mod_cast hq2
  have hq1 : (q : ℝ)-1 ≠ 0 := ne_of_gt (by linarith)
  have hq2' : (q : ℝ)-2 ≠ 0 := ne_of_gt (by linarith)
  simp only [mixedPairDenominator_eq_truncated]
  apply truncatedProductMass_local_comparison P _ _ q z Z hq.pos hqP
    (fun p hp => pairLocalWeight_nonneg a p ha (hP p hp))
    (fun p hp => pairLocalWeight_nonneg (q*a) p (dvd_mul_of_dvd_right ha q) (hP p hp)) ?_
    (((q : ℝ)-1)/((q : ℝ)-2)) (div_nonneg (by linarith) (by linarith)) ?_ hz
  · intro p hp
    have hpq := (mem_erase.mp hp).1
    have hpr := hP p (mem_erase.mp hp).2
    have he : p ∣ q*a ↔ p ∣ a := by
      rw [hpr.dvd_mul]
      have hn : ¬p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hpr hq).mp h)
      simp only [hn,false_or]
    simp only [pairLocalWeight,pairRootMultiplicity,he]
  · simp only [pairLocalWeight,pairRootMultiplicity,if_neg hqa,
      dvd_mul_right,if_true,Nat.cast_ofNat,Nat.cast_one]
    field_simp
    ring

/-- A finite pool costs only the sum of its prime labels in logarithmic
length. This coarse fixed loss does not change an asymptotic sieve constant. -/
theorem mixedPairDenominator_finite_local_lower (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2<q) (a L : ℕ) (ha : 0<a) (h2a : 2 ∣ a)
    (hL : finiteLocalLength Q ≤ L) :
    ((a.totient : ℝ)/(a : ℝ))*(((L-finiteLocalLength Q : ℕ) : ℝ)*Real.log 2)^2/2 ≤
      finiteLocalCorrection Q a*mixedPairDenominator a (2^L) (2^L+1).primesBelow := by
  induction Q using Finset.induction_on generalizing a L with
  | empty =>
    simpa only [finiteLocalLength,sum_empty,Nat.sub_zero,finiteLocalCorrection,prod_empty,one_mul]
      using mixedPairDenominator_dyadic_lower a L ha h2a
  | @insert q Q hqQ ih =>
    obtain ⟨hq,hq2⟩ := hQ q (mem_insert_self _ _)
    have hQ' : ∀ p ∈ Q, p.Prime ∧ 2<p := fun p hp => hQ p (mem_insert_of_mem hp)
    have hlen : finiteLocalLength (insert q Q)=q+finiteLocalLength Q := by
      simp only [finiteLocalLength,sum_insert hqQ]
    rw [hlen] at hL ⊢
    rw [finiteLocalCorrection,prod_insert hqQ]
    change _ ≤ (if q ∣ a then 1 else singularCorrection q)*finiteLocalCorrection Q a*_
    by_cases hqa : q ∣ a
    · rw [if_pos hqa,one_mul]
      apply le_trans _ (ih hQ' a L ha h2a (by omega))
      gcongr
      omega
    · rw [if_neg hqa]
      let z := 2^(L-q)
      let Z := 2^L
      let P := (Z+1).primesBelow
      have hqL : q ≤ L := by omega
      have hzZ : z ≤ Z := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
      have hqP : q ∈ P := Nat.mem_primesBelow.mpr ⟨by
        have hh := (Nat.lt_two_pow_self (n := q)).trans_le
          (Nat.pow_le_pow_right (by decide) hqL)
        change q < 2^L+1
        omega,hq⟩
      have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
      have hprod : q*z ≤ Z := by
        calc
          _ ≤ 2^q*z := Nat.mul_le_mul_right z (Nat.lt_two_pow_self (n := q)).le
          _ = Z := by dsimp [z,Z]; rw [← pow_add]; congr 1; omega
      have hcomp := mixedPairDenominator_local_comparison a q z Z P h2a hq hq2 hqa hP hqP hprod
      have hmono := mixedPairDenominator_mono_pool (q*a) z (z+1).primesBelow P
        (dvd_mul_of_dvd_right h2a q) hP (by
          intro p hp
          obtain ⟨hpz,hpr⟩ := Nat.mem_primesBelow.mp hp
          exact Nat.mem_primesBelow.mpr ⟨by omega,hpr⟩)
      have hlower := ih hQ' (q*a) (L-q) (Nat.mul_pos hq.pos ha)
        (dvd_mul_of_dvd_right h2a q) (by omega)
      have hphi : ((q*a).totient : ℝ)/((q*a : ℕ) : ℝ) =
          (((q : ℝ)-1)/(q : ℝ))*((a.totient : ℝ)/(a : ℝ)) := by
        rw [Nat.totient_mul (hq.coprime_iff_not_dvd.mpr hqa),Nat.totient_prime hq]
        rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_sub hq.one_lt.le,Nat.cast_one]
        ring
      rw [hphi,finiteLocalCorrection_prime_mul Q q a (fun p hp => (hQ' p hp).1) hq hqQ,
        Nat.sub_sub] at hlower
      have hc : 0 < finiteLocalCorrection Q a := finiteLocalCorrection_pos Q a (fun p hp => (hQ' p hp).2)
      have hqR : (2 : ℝ)<q := by exact_mod_cast hq2
      have hq0 : (q : ℝ) ≠ 0 := ne_of_gt (by linarith)
      have hq1 : (q : ℝ)-1 ≠ 0 := ne_of_gt (by linarith)
      have hq2' : (q : ℝ)-2 ≠ 0 := ne_of_gt (by linarith)
      have hqdiv : (0 : ℝ) ≤ (q : ℝ)/((q : ℝ)-1) := div_nonneg (Nat.cast_nonneg q) (by linarith)
      have hscaled := mul_le_mul_of_nonneg_left (hlower.trans
        (mul_le_mul_of_nonneg_left hmono hc.le))
        hqdiv
      have heq : (q : ℝ)/((q : ℝ)-1)*finiteLocalCorrection Q a*mixedPairDenominator (q*a) z P =
          singularCorrection q*finiteLocalCorrection Q a*
            ((((q : ℝ)-1)/((q : ℝ)-2))*mixedPairDenominator (q*a) z P) := by
        unfold singularCorrection
        field_simp
      have hlast := mul_le_mul_of_nonneg_left hcomp
        (mul_nonneg (singularCorrection_bounds q hq2).1.le hc.le)
      change _ ≤ singularCorrection q*finiteLocalCorrection Q a*mixedPairDenominator a Z P
      apply le_trans _ hlast
      rw [← heq]
      convert hscaled using 1 <;> field_simp

end Erdos821.Sieve
