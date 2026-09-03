import Submission.RecordLogBudget

/-!
# Lower bounds for logarithmic overlap inside squarefree totient fibers

These identities and finite inequalities are unconditional. The lower pair
bound retains the total logarithmic weight of the available input-prime pool;
no estimate making that weight small enough for exponent amplification is
assumed implicitly.
-/

open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.LogarithmicOverlap
set_option maxHeartbeats 2500000

noncomputable def primeWeight (p : ℕ) : ℝ := Real.log ((p-1 : ℕ) : ℝ)
noncomputable def poolWeight (P : Finset ℕ) : ℝ := ∑ p ∈ P, primeWeight p
noncomputable def incidence (F : Finset ℕ) (p : ℕ) : ℕ := (F.filter (fun a => p ∣ a)).card
noncomputable def overlap (F : Finset ℕ) : ℝ :=
  ∑ a ∈ F, ∑ b ∈ F, Real.log (totient (Nat.gcd a b) : ℝ)
noncomputable def largePairs (F : Finset ℕ) (n : ℕ) (η : ℝ) : Finset (ℕ × ℕ) :=
  (F ×ˢ F).filter (fun ab => (n : ℝ)^η ≤ (totient (Nat.gcd ab.1 ab.2) : ℝ))

lemma primeWeight_nonneg (p : ℕ) : 0 ≤ primeWeight p := Real.log_natCast_nonneg _
lemma poolWeight_nonneg (P : Finset ℕ) : 0 ≤ poolWeight P :=
  sum_nonneg (fun p _ => primeWeight_nonneg p)

lemma squarefree_log_totient_pool (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a : ℕ) (ha : Squarefree a) (hcut : a.primeFactors ⊆ P) :
    Real.log (totient a : ℝ) = ∑ p ∈ P, if p ∣ a then primeWeight p else 0 := by
  have he : totient a = ∏ p ∈ a.primeFactors, (p-1) := by
    rw [← totient_prod_primes a.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp), Nat.prod_primeFactors_of_squarefree ha]
  have hset : P.filter (fun p => p ∣ a) = a.primeFactors := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpP, hpa⟩ := mem_filter.mp hp
      exact (hP p hpP).mem_primeFactors hpa ha.ne_zero
    · intro hp
      exact mem_filter.mpr ⟨hcut hp, Nat.dvd_of_mem_primeFactors hp⟩
  rw [← sum_filter, hset, he, Nat.cast_prod, Real.log_prod]
  · rfl
  · intro p hp
    exact_mod_cast (Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt).ne'

lemma fiber_incidence_identity (F P : Finset ℕ) (n : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hF : ∀ a ∈ F, Squarefree a ∧ totient a=n ∧ a.primeFactors ⊆ P) :
    (F.card : ℝ)*Real.log (n : ℝ) = ∑ p ∈ P, primeWeight p*(incidence F p : ℝ) := by
  calc
    _ = ∑ _a ∈ F, Real.log (n : ℝ) := by simp
    _ = ∑ a ∈ F, ∑ p ∈ P, if p ∣ a then primeWeight p else 0 := by
      apply sum_congr rfl
      intro a ha
      rw [← (hF a ha).2.1]
      exact squarefree_log_totient_pool P hP a (hF a ha).1 (hF a ha).2.2
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p hp
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
      rfl

lemma gcd_log_totient_pool (F P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hF : ∀ a ∈ F, Squarefree a ∧ a.primeFactors ⊆ P)
    (a b : ℕ) (ha : a ∈ F) (_hb : b ∈ F) :
    Real.log (totient (Nat.gcd a b) : ℝ) =
      ∑ p ∈ P, if p ∣ a ∧ p ∣ b then primeWeight p else 0 := by
  have hs : Squarefree (Nat.gcd a b) :=
    (hF a ha).1.squarefree_of_dvd (Nat.gcd_dvd_left _ _)
  have hcut : (Nat.gcd a b).primeFactors ⊆ P := by
    intro p hp
    exact (hF a ha).2 ((Nat.prime_of_mem_primeFactors hp).mem_primeFactors
      ((Nat.dvd_of_mem_primeFactors hp).trans (Nat.gcd_dvd_left _ _)) (hF a ha).1.ne_zero)
  simpa only [Nat.dvd_gcd_iff] using squarefree_log_totient_pool P hP (Nat.gcd a b) hs hcut

/-- Exact second-moment identity; no independence of prime incidences is used. -/
theorem overlap_incidence_identity (F P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hF : ∀ a ∈ F, Squarefree a ∧ a.primeFactors ⊆ P) :
    overlap F = ∑ p ∈ P, primeWeight p*(incidence F p : ℝ)^2 := by
  have h1 : overlap F = ∑ a ∈ F, ∑ b ∈ F,
      ∑ p ∈ P, if p ∣ a ∧ p ∣ b then primeWeight p else 0 := by
    apply sum_congr rfl
    intro a ha
    exact sum_congr rfl (fun b hb => gcd_log_totient_pool F P hP hF a b ha hb)
  rw [h1]
  calc
    _ = ∑ p ∈ P, ∑ a ∈ F, ∑ b ∈ F,
        if p ∣ a ∧ p ∣ b then primeWeight p else 0 := by
      simp_rw [sum_comm (s := F) (t := P)]
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      have hi (a : ℕ) : (∑ b ∈ F, if p ∣ a ∧ p ∣ b then primeWeight p else 0) =
          if p ∣ a then (incidence F p : ℝ)*primeWeight p else 0 := by
        by_cases hpa : p ∣ a
        · simp only [hpa, true_and, if_true]
          rw [← sum_filter, sum_const, nsmul_eq_mul]
          rfl
        · simp [hpa]
      simp_rw [hi]
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      change (incidence F p : ℝ)*((incidence F p : ℝ)*primeWeight p) = _
      ring

/-- Weighted Cauchy--Schwarz gives a genuine lower overlap bound. -/
theorem fiber_log_square_le_pool_mul_overlap (F P : Finset ℕ) (n : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hF : ∀ a ∈ F, Squarefree a ∧ totient a=n ∧ a.primeFactors ⊆ P) :
    ((F.card : ℝ)*Real.log (n : ℝ))^2 ≤ poolWeight P*overlap F := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq P
    (fun p => Real.sqrt (primeWeight p))
    (fun p => Real.sqrt (primeWeight p)*(incidence F p : ℝ))
  have hi : (∑ p ∈ P, Real.sqrt (primeWeight p)*
      (Real.sqrt (primeWeight p)*(incidence F p : ℝ))) =
      ∑ p ∈ P, primeWeight p*(incidence F p : ℝ) := by
    apply sum_congr rfl
    intro p hp
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (primeWeight_nonneg p)]
  simp_rw [mul_pow, Real.sq_sqrt (primeWeight_nonneg _)] at hc
  rw [hi, ← fiber_incidence_identity F P n hP hF,
    ← overlap_incidence_identity F P hP (fun a ha => ⟨(hF a ha).1, (hF a ha).2.2⟩)] at hc
  exact hc

lemma overlap_le_large_pair_count (F : Finset ℕ) (n : ℕ) (hn : 1 < n)
    (hF : ∀ a ∈ F, Squarefree a ∧ totient a=n) (η : ℝ) :
    overlap F ≤ η*Real.log (n : ℝ)*(F.card : ℝ)^2 +
      (1-η)*Real.log (n : ℝ)*((largePairs F n η).card : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hb (ab : ℕ × ℕ) (hab : ab ∈ F ×ˢ F) :
      Real.log (totient (Nat.gcd ab.1 ab.2) : ℝ) ≤ η*Real.log (n : ℝ)+
        (if (n : ℝ)^η ≤ (totient (Nat.gcd ab.1 ab.2) : ℝ) then
          (1-η)*Real.log (n : ℝ) else 0) := by
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    have hapos : 0 < ab.1 := Nat.pos_of_ne_zero (hF ab.1 ha).1.ne_zero
    have hdpos : 0 < totient (Nat.gcd ab.1 ab.2) :=
      Nat.totient_pos.mpr (Nat.gcd_pos_of_pos_left _ hapos)
    have hdR : (0 : ℝ) < totient (Nat.gcd ab.1 ab.2) := by exact_mod_cast hdpos
    have hdn : totient (Nat.gcd ab.1 ab.2) ≤ n := by
      rw [← (hF ab.1 ha).2]
      exact Nat.le_of_dvd (Nat.totient_pos.mpr hapos)
        (Nat.totient_dvd_of_dvd (Nat.gcd_dvd_left _ _))
    split_ifs with he
    · have hh : Real.log (totient (Nat.gcd ab.1 ab.2) : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log hdR (by exact_mod_cast hdn)
      nlinarith only [hh]
    · have hh := Real.log_le_log hdR (le_of_lt (lt_of_not_ge he))
      rw [Real.log_rpow hnR] at hh
      linarith only [hh]
  calc
    overlap F = ∑ ab ∈ F ×ˢ F, Real.log (totient (Nat.gcd ab.1 ab.2) : ℝ) := by
      simp only [overlap, sum_product]
    _ ≤ ∑ ab ∈ F ×ˢ F, (η*Real.log (n : ℝ)+
        (if (n : ℝ)^η ≤ (totient (Nat.gcd ab.1 ab.2) : ℝ) then
          (1-η)*Real.log (n : ℝ) else 0)) := sum_le_sum hb
    _ = _ := by
      rw [sum_add_distrib, ← sum_filter]
      simp only [sum_const, nsmul_eq_mul, card_product, Nat.cast_mul, largePairs]
      ring

/-- A finite lower bound on the number of pairs above an overlap threshold.
The input-prime-pool weight remains explicit. -/
theorem lower_large_pair_count (F P : Finset ℕ) (n : ℕ) (hn : 1 < n)
    (hP : ∀ p ∈ P, p.Prime)
    (hF : ∀ a ∈ F, Squarefree a ∧ totient a=n ∧ a.primeFactors ⊆ P)
    (η : ℝ) :
    (F.card : ℝ)^2*(Real.log (n : ℝ)-η*poolWeight P) ≤
      (1-η)*poolWeight P*((largePairs F n η).card : ℝ) := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have h1 := fiber_log_square_le_pool_mul_overlap F P n hP hF
  have h2 := mul_le_mul_of_nonneg_left
    (overlap_le_large_pair_count F n hn (fun a ha => ⟨(hF a ha).1, (hF a ha).2.1⟩) η)
    (poolWeight_nonneg P)
  apply (mul_le_mul_iff_left₀ hlog).mp
  nlinarith only [h1.trans h2]

/-- A compact logarithmic pool would give a positive pair proportion when
C*eta<1. No such compact-pool hypothesis is proved for large fibers. -/
theorem lower_large_pair_count_of_pool_bound (F P : Finset ℕ) (n : ℕ) (hn : 1 < n)
    (hP : ∀ p ∈ P, p.Prime)
    (hF : ∀ a ∈ F, Squarefree a ∧ totient a=n ∧ a.primeFactors ⊆ P)
    (C η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hW : poolWeight P ≤ C*Real.log (n : ℝ)) :
    (1-C*η)*(F.card : ℝ)^2 ≤ C*(1-η)*((largePairs F n η).card : ℝ) := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have h1 := fiber_log_square_le_pool_mul_overlap F P n hP hF
  have h2 := mul_le_mul_of_nonneg_left
    (overlap_le_large_pair_count F n hn (fun a ha => ⟨(hF a ha).1, (hF a ha).2.1⟩) η)
    (poolWeight_nonneg P)
  have hone : 0 ≤ 1-η := sub_nonneg.mpr hη1
  have h3 := mul_le_mul_of_nonneg_right hW
    (show 0 ≤ η*Real.log (n : ℝ)*(F.card : ℝ)^2 +
      (1-η)*Real.log (n : ℝ)*((largePairs F n η).card : ℝ) by positivity)
  have h4 : (1-C*η)*(F.card : ℝ)^2*(Real.log (n : ℝ))^2 ≤
      C*(1-η)*((largePairs F n η).card : ℝ)*(Real.log (n : ℝ))^2 := by
    nlinarith only [h1.trans (h2.trans h3)]
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hlog)).mp h4

end Erdos821.LogarithmicOverlap
