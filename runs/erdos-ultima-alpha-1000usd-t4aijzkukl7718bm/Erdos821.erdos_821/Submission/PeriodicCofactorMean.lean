import Submission.RestrictedCofactorWeights
import Submission.RestrictedRelativeMean

/-!
# Density-free relative means from exact cofactor periodicity

For a nonnegative weight supported on primes, averaging a long cofactor
prefix gives a relative error involving only its length, the modulus
cutoff, and the reciprocal size of the input primes. No lower bound on
the restricted mass is needed. The cofactor average is not removed.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma residue_prefix_range_error (d B : ℕ) [NeZero d] (z : ZMod d) :
    |(∑ a ∈ range B, if (a : ZMod d)=z then (1 : ℝ) else 0)-(B : ℝ)/d| ≤ 1 := by
  have hh := Sieve.abs_card_residue_filter_sub B d (NeZero.pos d) {z.val}
    (fun r hr => by simpa only [mem_singleton] using (mem_singleton.mp hr) ▸ z.val_lt)
  have he (a : ℕ) : a%d=z.val ↔ (a : ZMod d)=z := by
    rw [← ZMod.val_natCast d a]
    exact (ZMod.val_injective d).eq_iff
  simpa only [mem_singleton,he,card_singleton,Nat.cast_one,mul_one,
    ← sum_filter,sum_const,nsmul_eq_mul] using hh

lemma residue_prefix_Icc_error (d B : ℕ) [NeZero d] (z : ZMod d) :
    |(∑ a ∈ Icc 1 B, if (a : ZMod d)=z then (1 : ℝ) else 0)-(B : ℝ)/d| ≤ 1 := by
  have hh := residue_prefix_range_error d B (z-1)
  have hset : Icc 1 B = Ico 1 (B+1) := by ext a; simp only [mem_Icc,mem_Ico]; omega
  rw [hset,sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
  have he (a : ℕ) : (1+(a : ZMod d)=z) ↔ (a : ZMod d)=z-1 := by
    constructor <;> intro h <;> linear_combination h
  simpa only [he] using hh

lemma unit_cofactor_prefix_error (d B n : ℕ) [NeZero d] (u : (ZMod d)ˣ)
    (hn : n.Coprime d) :
    |(∑ a ∈ Icc 1 B, if (u : ZMod d)*(a : ZMod d)*(n : ZMod d)=1 then (1 : ℝ) else 0)-
      (B : ℝ)/d| ≤ 1 := by
  have hnU : IsUnit (n : ZMod d) := (ZMod.isUnit_iff_coprime n d).mpr hn
  let v : (ZMod d)ˣ := u*hnU.unit
  have hv : (v : ZMod d)=(u : ZMod d)*(n : ZMod d) := by simp [v]
  have he (a : ℕ) : (u : ZMod d)*(a : ZMod d)*(n : ZMod d)=1 ↔
      (a : ZMod d)=(↑(v⁻¹) : ZMod d) := by
    rw [show (u : ZMod d)*(a : ZMod d)*(n : ZMod d)=(v : ZMod d)*(a : ZMod d) by rw [hv]; ring]
    have hh := Units.mul_right_inj v (b := (a : ZMod d)) (c := (↑(v⁻¹) : ZMod d))
    simpa using hh
  simpa only [he] using residue_prefix_Icc_error d B (↑(v⁻¹) : ZMod d)

lemma nonunit_cofactor_prefix_zero (d B n : ℕ) (u : (ZMod d)ˣ)
    (hn : ¬n.Coprime d) :
    (∑ a ∈ Icc 1 B, if (u : ZMod d)*(a : ZMod d)*(n : ZMod d)=1 then (1 : ℝ) else 0)=0 := by
  apply sum_eq_zero
  intro a ha
  have hnot : (u : ZMod d)*(a : ZMod d)*(n : ZMod d) ≠ 1 := by
    intro h
    exact hn ((ZMod.isUnit_iff_coprime n d).mp (IsUnit.of_mul_eq_one_right _ h))
  simp only [hnot,if_false]

lemma cofactor_prefix_error (d B n : ℕ) [NeZero d] (u : (ZMod d)ˣ) :
    |(∑ a ∈ Icc 1 B, if (u : ZMod d)*(a : ZMod d)*(n : ZMod d)=1 then (1 : ℝ) else 0)-
      (B : ℝ)/d| ≤ 1+(if ¬n.Coprime d then (B : ℝ)/d else 0) := by
  by_cases hn : n.Coprime d
  · rw [if_neg (not_not.mpr hn),add_zero]
    exact unit_cofactor_prefix_error d B n u hn
  · rw [nonunit_cofactor_prefix_zero d B n u hn,zero_sub,abs_neg,abs_of_nonneg (by positivity),if_pos hn]
    linarith

/-- A single residue class contributes one endpoint error per input weight.
Nonunit inputs have their exact separate correction. -/
theorem periodic_cofactor_single_modulus (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (d : ℕ) [NeZero d] (u : (ZMod d)ˣ) (B N : ℕ) :
    |restrictedCofactorWeight f d u 0 B N-(B : ℝ)*restrictedMass f N/(d : ℝ)| ≤
      restrictedMass f N+(B : ℝ)*restrictedNonunitMass f d N/(d : ℝ) := by
  have he : restrictedCofactorWeight f d u 0 B N-(B : ℝ)*restrictedMass f N/(d : ℝ) =
      ∑ n ∈ Icc 1 N, f n*((∑ a ∈ Icc 1 B,
        if (u : ZMod d)*(a : ZMod d)*(n : ZMod d)=1 then (1 : ℝ) else 0)-(B : ℝ)/d) := by
    unfold restrictedCofactorWeight restrictedMass
    rw [sum_comm]
    simp only [zero_add,mul_sub,mul_sum,sum_sub_distrib,sum_div]
    congr 1
    · apply sum_congr rfl
      intro n hn
      apply sum_congr rfl
      intro a ha
      split_ifs <;> ring
    · apply sum_congr rfl
      intro n hn
      ring
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Icc 1 N, f n*(1+(if ¬n.Coprime d then (B : ℝ)/d else 0)) := by
      apply sum_le_sum
      intro n hn
      rw [abs_mul,abs_of_nonneg (hf n)]
      exact mul_le_mul_of_nonneg_left (cofactor_prefix_error d B n u) (hf n)
    _ = _ := by
      simp only [mul_add,mul_one,sum_add_distrib,restrictedMass,restrictedNonunitMass,mul_sum,sum_div]
      congr 1
      apply sum_congr rfl
      intro n hn
      split_ifs <;> ring

noncomputable def primeReciprocalMass (f : ArithmeticFunction ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, f n/(n : ℝ)

/-- Prime support gives a reciprocal-prime, rather than ambient, nonunit error. -/
lemma prime_weight_nonunit_mean (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (hprime : ∀ n, f n ≠ 0 → n.Prime) (Q N : ℕ) :
    (∑ d ∈ Icc 1 Q, restrictedNonunitMass f d N/(d : ℝ)) ≤
      (harmonic Q : ℝ)*primeReciprocalMass f N := by
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      (∑ d ∈ Icc 1 Q, (if ¬n.Coprime d then f n else 0)/(d : ℝ)) ≤
        (harmonic Q : ℝ)*(f n/(n : ℝ)) := by
    by_cases hz : f n=0
    · simp [hz]
    have hp := hprime n hz
    have he : (∑ d ∈ Icc 1 Q, (if ¬n.Coprime d then f n else 0)/(d : ℝ)) =
        f n*(∑ d ∈ Icc 1 Q with n ∣ d, (d : ℝ)⁻¹) := by
      rw [sum_filter,mul_sum]
      apply sum_congr rfl
      intro d hd
      simp only [hp.coprime_iff_not_dvd,not_not]
      split_ifs <;> simp [div_eq_mul_inv]
    rw [he]
    have hh := mul_le_mul_of_nonneg_left (Sieve.sum_inv_multiples_le_harmonic Q n hp.pos) (hf n)
    convert hh using 1; ring
  simp only [restrictedNonunitMass,sum_div]
  rw [sum_comm]
  apply (sum_le_sum hpoint).trans_eq
  simp only [primeReciprocalMass,mul_sum]

/-- Density-free: the mass may be arbitrarily small, and f need not be
bounded by the von Mangoldt function. -/
theorem periodic_prime_cofactor_mean (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (hprime : ∀ n, f n ≠ 0 → n.Prime) (Q B N : ℕ) (u : ∀ d : ℕ, (ZMod d)ˣ) :
    (∑ d ∈ Icc 1 Q, |restrictedCofactorWeight f d (u d) 0 B N-
      (B : ℝ)*restrictedMass f N/(d : ℝ)|) ≤
        (Q : ℝ)*restrictedMass f N+(B : ℝ)*(harmonic Q : ℝ)*primeReciprocalMass f N := by
  have hh : (∑ d ∈ Icc 1 Q, |restrictedCofactorWeight f d (u d) 0 B N-
      (B : ℝ)*restrictedMass f N/(d : ℝ)|) ≤
      (Q : ℝ)*restrictedMass f N+(B : ℝ)*
        (∑ d ∈ Icc 1 Q, restrictedNonunitMass f d N/(d : ℝ)) := by
    have hp (d : ℕ) (hd : d ∈ Icc 1 Q) :
        |restrictedCofactorWeight f d (u d) 0 B N-(B : ℝ)*restrictedMass f N/(d : ℝ)| ≤
          restrictedMass f N+(B : ℝ)*restrictedNonunitMass f d N/(d : ℝ) := by
      letI : NeZero d := ⟨by have := (mem_Icc.mp hd).1; omega⟩
      exact periodic_cofactor_single_modulus f hf d (u d) B N
    apply (sum_le_sum hp).trans_eq
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
    rw [mul_sum]
    congr 1
    apply sum_congr rfl
    intro d hd
    ring
  apply hh.trans
  have hb := mul_le_mul_of_nonneg_left (prime_weight_nonunit_mean f hf hprime Q N) (Nat.cast_nonneg B)
  simpa only [mul_assoc] using _root_.add_le_add le_rfl hb

lemma primeReciprocalMass_le (f : ArithmeticFunction ℝ) (hf : ∀ n, 0 ≤ f n)
    (Z N : ℕ) (hZ : 0 < Z) (hsupport : ∀ n, f n ≠ 0 → Z ≤ n) :
    primeReciprocalMass f N ≤ restrictedMass f N/(Z : ℝ) := by
  unfold primeReciprocalMass restrictedMass
  rw [sum_div]
  apply sum_le_sum
  intro n hn
  by_cases hz : f n=0
  · simp [hz]
  exact div_le_div_of_nonneg_left (hf n) (by exact_mod_cast hZ)
    (by exact_mod_cast hsupport n hz)

/-- If all input primes are at least Z, the relative error is bounded by
Q/B + H(Q)/Z. This is useful when the cofactor is longer than the moduli. -/
theorem periodic_prime_cofactor_relative_bound (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (Q B N Z : ℕ) (hZ : 0 < Z)
    (hsupport : ∀ n, f n ≠ 0 → n.Prime ∧ Z ≤ n) (u : ∀ d : ℕ, (ZMod d)ˣ) :
    (∑ d ∈ Icc 1 Q, |restrictedCofactorWeight f d (u d) 0 B N-
      (B : ℝ)*restrictedMass f N/(d : ℝ)|) ≤
        ((Q : ℝ)+(B : ℝ)*(harmonic Q : ℝ)/(Z : ℝ))*restrictedMass f N := by
  apply (periodic_prime_cofactor_mean f hf (fun n hn => (hsupport n hn).1) Q B N u).trans
  have hh := mul_le_mul_of_nonneg_left (primeReciprocalMass_le f hf Z N hZ (fun n hn => (hsupport n hn).2))
    (mul_nonneg (Nat.cast_nonneg B) (harmonic_natCast_nonneg Q))
  have hh' := _root_.add_le_add (le_refl ((Q : ℝ)*restrictedMass f N)) hh
  convert hh' using 1; ring

end Erdos821.AnalyticSieve
