import Submission.MultiplicativeChirpObstruction

/-! Stripping finitely many prime phases makes multiplier invariance exact.
The resulting models retain a nonzero natural adjacent imaginary bias. This
is an obstruction to an abstract strategy, not to the max-prime conjecture. -/
namespace Erdos371.ExactMultiplierChirpObstruction
open Finset Filter MultiplicativeChirpObstruction
open scoped Topology

noncomputable def strippedChirp (t : ℝ) (B n : ℕ) : ℂ :=
  chirp t n * ∏ p ∈ (B+1).primesBelow, (starRingEnd ℂ) (chirp t p) ^ n.factorization p

lemma chirp_norm_eq_one (t : ℝ) (n : ℕ) (hn : n ≠ 0) : ‖chirp t n‖ = 1 := by
  rw [chirp_apply t n hn, Complex.norm_exp_ofReal_mul_I]

lemma strippedChirp_zero (t : ℝ) (B : ℕ) : strippedChirp t B 0 = 0 := by
  simp [strippedChirp]

lemma strippedChirp_norm_le_one (t : ℝ) (B n : ℕ) : ‖strippedChirp t B n‖ ≤ 1 := by
  rw [strippedChirp, norm_mul, norm_prod]
  have hp : (∏ p ∈ (B+1).primesBelow, ‖(starRingEnd ℂ) (chirp t p) ^ n.factorization p‖) = 1 := by
    apply prod_eq_one
    intro p hp
    rw [norm_pow, Complex.norm_conj, chirp_norm_eq_one t p (Nat.mem_primesBelow.mp hp).2.ne_zero,
      one_pow]
  rw [hp,mul_one]
  exact chirp_norm_le_one t n

lemma strippedChirp_mul (t : ℝ) (B a b : ℕ) :
    strippedChirp t B (a*b) = strippedChirp t B a * strippedChirp t B b := by
  by_cases ha : a = 0
  · subst a; simp [strippedChirp_zero]
  by_cases hb : b = 0
  · subst b; simp [strippedChirp_zero]
  simp only [strippedChirp, map_mul, Nat.factorization_mul ha hb, Finsupp.add_apply,
    pow_add, prod_mul_distrib]
  ring

lemma chirp_factorization (t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors, chirp t p ^ n.factorization p) = chirp t n := by
  have he := congrArg (chirp t) (Nat.factorization_prod_pow_eq_self hn)
  simpa only [Finsupp.prod, Nat.support_factorization, map_prod, map_pow] using he

lemma strippedChirp_small (t : ℝ) (B k : ℕ) (hk : 0 < k) (hkB : k ≤ B) :
    strippedChirp t B k = 1 := by
  have hsub : k.primeFactors ⊆ (B+1).primesBelow := by
    intro p hp
    obtain ⟨hpp,hpd,_⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primesBelow.mpr ⟨lt_of_le_of_lt ((Nat.le_of_dvd hk hpd).trans hkB) (Nat.lt_succ_self B), hpp⟩
  have he : (∏ p ∈ (B+1).primesBelow, (starRingEnd ℂ) (chirp t p) ^ k.factorization p) =
      (starRingEnd ℂ) (chirp t k) := by
    rw [← chirp_factorization t k hk.ne', map_prod]
    simp only [map_pow]
    symm
    apply prod_subset hsub
    intro p _ hp
    have hz : k.factorization p = 0 := by
      simpa only [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] using hp
    simp [hz]
  rw [strippedChirp,he,Complex.mul_conj,Complex.normSq_eq_norm_sq,chirp_norm_eq_one t k hk.ne']
  norm_num

/-- Exact invariance holds at every starting integer, including zero. -/
theorem strippedChirp_small_multiplier (t : ℝ) (B k n : ℕ) (hk : 0 < k) (hkB : k ≤ B) :
    strippedChirp t B (k*n) = strippedChirp t B n := by
  rw [strippedChirp_mul, strippedChirp_small t B k hk hkB, one_mul]

lemma norm_mul_sub_one_le (z u : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖z*u-1‖ ≤ ‖z-1‖+‖u-1‖ := by
  calc
    _ = ‖(z-1)+z*(u-1)‖ := by congr 1; ring
    _ ≤ ‖z-1‖+‖z*(u-1)‖ := norm_add_le _ _
    _ ≤ _ := by rw [norm_mul]; gcongr; exact mul_le_of_le_one_left (norm_nonneg _) hz

lemma norm_pow_sub_one_le (z : ℂ) (hz : ‖z‖ ≤ 1) (k : ℕ) :
    ‖z^k-1‖ ≤ k*‖z-1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    have hb := norm_mul_sub_one_le z (z^k) hz
    push_cast
    linarith

lemma norm_prod_sub_one_le {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1) :
    ‖(∏ i ∈ S, z i)-1‖ ≤ ∑ i ∈ S, ‖z i-1‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [prod_insert ha,sum_insert ha]
    exact (norm_mul_sub_one_le (z a) (∏ i ∈ S, z i) (hz a (mem_insert_self _ _))).trans
      (add_le_add_right (ih (fun i hi => hz i (mem_insert_of_mem hi))) _)

lemma strippedChirp_error (t : ℝ) (B n : ℕ) :
    ‖strippedChirp t B n-chirp t n‖ ≤
      ∑ p ∈ (B+1).primesBelow, (n.factorization p : ℝ)*‖chirp t p-1‖ := by
  let z := fun p : ℕ => (starRingEnd ℂ) (chirp t p)
  have hz (p : ℕ) : ‖z p‖ ≤ 1 := by simpa only [z,Complex.norm_conj] using chirp_norm_le_one t p
  have hp := norm_prod_sub_one_le (B+1).primesBelow (fun p => z p^n.factorization p)
    (fun p _ => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hz p))
  have he (p : ℕ) : ‖z p-1‖ = ‖chirp t p-1‖ := by
    rw [show z p-1 = (starRingEnd ℂ) (chirp t p-1) by simp [z],Complex.norm_conj]
  have hb : ‖(∏ p ∈ (B+1).primesBelow, z p^n.factorization p)-1‖ ≤
      ∑ p ∈ (B+1).primesBelow, (n.factorization p : ℝ)*‖chirp t p-1‖ :=
    hp.trans (sum_le_sum fun p _ => by simpa only [he] using norm_pow_sub_one_le (z p) (hz p) _)
  unfold strippedChirp
  rw [show chirp t n * (∏ p ∈ (B+1).primesBelow, z p^n.factorization p)-chirp t n =
    chirp t n*((∏ p ∈ (B+1).primesBelow, z p^n.factorization p)-1) by ring, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (chirp_norm_le_one t n)).trans hb

lemma sum_factorization_le (N p : ℕ) (hp : p.Prime) :
    (∑ n ∈ Icc 1 N, (n.factorization p : ℝ)) ≤ N := by
  letI : Fact p.Prime := ⟨hp⟩
  have he : ∑ n ∈ Icc 1 N, n.factorization p = N.factorial.factorization p := by
    rw [← Nat.factorization_prod_apply (fun n hn => by have := (mem_Icc.mp hn).1; omega)]
    have hprod : (∏ n ∈ Icc 1 N, n) = N.factorial := by
      induction N with
      | zero => simp
      | succ N ih => rw [prod_Icc_succ_top (by omega), ih, Nat.factorial_succ, mul_comm]
    rw [hprod]
  have hb := padicValNat_factorial_le p N
  rw [← Nat.factorization_def N.factorial hp] at hb
  exact_mod_cast (he.trans_le hb)

lemma strippedChirp_error_sum (t : ℝ) (B N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖strippedChirp t B n-chirp t n‖) ≤
      N*(∑ p ∈ (B+1).primesBelow, ‖chirp t p-1‖) := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ p ∈ (B+1).primesBelow,
        (n.factorization p : ℝ)*‖chirp t p-1‖ := sum_le_sum fun n _ => strippedChirp_error t B n
    _ = ∑ p ∈ (B+1).primesBelow, (∑ n ∈ Icc 1 N, (n.factorization p : ℝ))*‖chirp t p-1‖ := by
      rw [sum_comm]
      simp only [sum_mul]
    _ ≤ ∑ p ∈ (B+1).primesBelow, (N : ℝ)*‖chirp t p-1‖ := by
      apply sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right (sum_factorization_le N p (Nat.mem_primesBelow.mp hp).2)
        (norm_nonneg _)
    _ = _ := (mul_sum ..).symm

#print axioms strippedChirp_small_multiplier
#print axioms strippedChirp_error_sum
end Erdos371.ExactMultiplierChirpObstruction
