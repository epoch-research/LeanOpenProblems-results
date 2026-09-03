import Submission.ElementarySquareSieve

/-!
A primorial version of the modular upper bound. Its exponent loss still tends to
zero, so it does not disprove Erdős 773.
-/

namespace Erdos773
open Finset

set_option maxHeartbeats 1000000

def sievePrimes (n : ℕ) : Finset ℕ :=
  (range (2 * n + 1)).filter (fun p => p.Prime ∧ 5 ≤ p)

def sievePrimorial (n : ℕ) : ℕ := ∏ p ∈ sievePrimes n, p

lemma sievePrimorial_pos (n : ℕ) : 0 < sievePrimorial n := by
  apply Finset.prod_pos
  intro p hp
  exact (mem_filter.mp hp).2.1.pos

lemma sievePrimorial_le (n : ℕ) : sievePrimorial n ≤ 4 ^ (2 * n) := by
  have hs : sievePrimes n ⊆ (range (2 * n + 1)).filter Nat.Prime := by
    intro p hp
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1, (mem_filter.mp hp).2.1⟩
  calc
    _ ≤ primorial (2 * n) := by
      apply Finset.prod_le_prod_of_subset_of_one_le' hs
      intro p hp _
      exact (mem_filter.mp hp).2.one_lt.le
    _ ≤ _ := primorial_le_4_pow _

lemma sievePrimes_card_le (n : ℕ) : (sievePrimes n).card ≤ 2 * n + 1 := by
  simpa using (card_filter_le (s := range (2 * n + 1))
    (p := fun p => p.Prime ∧ 5 ≤ p))

lemma centralBinom_two_pow_le (n : ℕ) : 2 ^ n ≤ Nat.centralBinom n := by
  by_cases hn : 4 ≤ n
  · have h := Nat.four_pow_lt_mul_centralBinom n hn
    have hn2 : n ≤ 2 ^ n := (Nat.lt_two_pow_self).le
    have he : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
      norm_num
    rw [he] at h
    have hpos : 0 < (2 : ℕ) ^ n := by positivity
    nlinarith
  · interval_cases n <;> decide

lemma centralBinom_le_prime_count_pow (n : ℕ) (hn : 0 < n) :
    Nat.centralBinom n ≤
      (2 * n) ^ ((range (2 * n + 1)).filter Nat.Prime).card := by
  have he : (∏ p ∈ (range (2 * n + 1)).filter Nat.Prime,
      p ^ (Nat.centralBinom n).factorization p) = Nat.centralBinom n := by
    rw [Finset.prod_filter_of_ne]
    · exact Nat.prod_pow_factorization_centralBinom n
    · intro p _ hp
      by_contra h
      simp [Nat.factorization_eq_zero_of_not_prime _ h] at hp
  rw [← he]
  calc
    _ ≤ ∏ _p ∈ (range (2 * n + 1)).filter Nat.Prime, (2 * n) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro p hp
      exact Nat.pow_factorization_choose_le (by omega : 0 < 2 * n)
    _ = _ := by simp

lemma sievePrimes_card_covers_prime_count (n : ℕ) :
    ((range (2 * n + 1)).filter Nat.Prime).card ≤ (sievePrimes n).card + 2 := by
  have hs : (range (2 * n + 1)).filter Nat.Prime ⊆ sievePrimes n ∪ {2, 3} := by
    intro p hp
    by_cases h5 : 5 ≤ p
    · exact mem_union_left _ (mem_filter.mpr ⟨(mem_filter.mp hp).1,
        (mem_filter.mp hp).2, h5⟩)
    · have hprime := (mem_filter.mp hp).2
      have hp2 : 2 ≤ p := hprime.two_le
      have hp4 : p ≠ 4 := by intro he; subst p; norm_num at hprime
      have : p = 2 ∨ p = 3 := by omega
      exact mem_union_right _ (by simpa using this)
  exact (card_le_card hs).trans (by
    have h := card_union_le (sievePrimes n) {2, 3}
    simpa using h)

lemma sievePrimes_card_log_lower (n : ℕ) (hn : 128 ≤ n) :
    (n : ℝ) / 8 ≤ (sievePrimes n).card * Real.log n := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn128 : (128 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hlog2' : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hlog128 : Real.log 128 ≤ 7 := by
    have he : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hnlog : Real.log n ≤ (n : ℝ) / 16 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hnp (by norm_num : (0 : ℝ) < 128))
    rw [Real.log_div hnp.ne' (by norm_num : (128 : ℝ) ≠ 0)] at h
    linarith
  have hlogn2 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by linarith)
  have hpow : (2 : ℕ) ^ n ≤ (2 * n) ^ ((sievePrimes n).card + 2) :=
    (centralBinom_two_pow_le n).trans ((centralBinom_le_prime_count_pow n (by omega)).trans
      (Nat.pow_le_pow_right (by omega) (sievePrimes_card_covers_prime_count n)))
  have hpowR : (2 : ℝ) ^ n ≤ (2 * (n : ℝ)) ^ ((sievePrimes n).card + 2) := by
    exact_mod_cast hpow
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ n) hpowR
  rw [Real.log_pow, Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnp.ne'] at hl
  push_cast at hl
  have h1 := mul_le_mul_of_nonneg_left hlog2 hnp.le
  have h2 := mul_le_mul_of_nonneg_left hlogn2
    (show (0 : ℝ) ≤ (sievePrimes n).card + 2 by positivity)
  nlinarith

lemma quadraticResidueDensity_prod_primes (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 5 ≤ p) :
    quadraticResidueDensity (∏ p ∈ S, p) ≤ (3 / 4 : ℝ) ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using quadraticResidueDensity_le_one 1
  | @insert p S hp ih =>
    have hp' := hS p (mem_insert_self _ _)
    have hS' : ∀ q ∈ S, q.Prime ∧ 5 ≤ q :=
      fun q hq => hS q (mem_insert_of_mem hq)
    letI : NeZero p := ⟨hp'.1.ne_zero⟩
    letI : NeZero (∏ q ∈ S, q) := ⟨(Finset.prod_pos
      (fun q hq => (hS' q hq).1.pos)).ne'⟩
    have hc : p.Coprime (∏ q ∈ S, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      apply (hp'.1.coprime_iff_not_dvd).mpr
      intro hd
      have he := (Nat.prime_dvd_prime_iff_eq hp'.1 (hS' q hq).1).mp hd
      exact hp (he ▸ hq)
    rw [prod_insert hp, card_insert_of_notMem hp, pow_succ]
    calc
      _ ≤ quadraticResidueDensity p * quadraticResidueDensity (∏ q ∈ S, q) :=
        quadraticResidueDensity_mul_le _ _ hc
      _ ≤ (3 / 4 : ℝ) * (3 / 4 : ℝ) ^ S.card :=
        mul_le_mul (quadraticResidueDensity_le_three_quarters _ (by omega)) (ih hS')
          (quadraticResidueDensity_nonneg _) (by norm_num)
      _ = _ := by ring

lemma sievePrimorial_density (n : ℕ) :
    quadraticResidueDensity (sievePrimorial n) ≤ (3 / 4 : ℝ) ^ (sievePrimes n).card :=
  quadraticResidueDensity_prod_primes _ (fun _ hp => (mem_filter.mp hp).2)

lemma square_sidon_upper_of_modulus (k N Q : ℕ) (hQ : 0 < Q)
    (hQN : 2 ^ k * Q ≤ N) (hd : quadraticResidueDensity Q ≤ (3 / 4 : ℝ) ^ k) :
    (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) ≤
      2 * (Real.sqrt (3 / 4) : ℝ) ^ k * N := by
  letI : NeZero Q := ⟨hQ.ne'⟩
  have hQN' : (2 : ℝ) ^ k * Q ≤ N := by exact_mod_cast hQN
  have hhalf := mul_le_mul_of_nonneg_left hQN' (by positivity : (0 : ℝ) ≤ (1 / 2) ^ k)
  have he : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
  rw [← mul_assoc, he, one_mul] at hhalf
  have hhalf34 : (1 / 2 : ℝ) ^ k ≤ (3 / 4 : ℝ) ^ k :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hQr : (Q : ℝ) ≤ (3 / 4 : ℝ) ^ k * N :=
    hhalf.trans (mul_le_mul_of_nonneg_right hhalf34 (Nat.cast_nonneg N))
  have hN1 : (1 : ℝ) ≤ N := by
    have hp : 0 < 2 ^ k * Q := by positivity
    exact_mod_cast hp.trans_le hQN
  have hs : ((quadraticResidues Q).card : ℝ) ≤ Q := by
    exact_mod_cast (by simpa using card_le_univ (quadraticResidues Q) :
      (quadraticResidues Q).card ≤ Q)
  have ht := mul_le_mul (hs.trans hQr) (show (N : ℝ) + 1 ≤ 2 * N by linarith)
    (by positivity : (0 : ℝ) ≤ N + 1) (by positivity : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ k * N)
  have hd' := mul_le_mul_of_nonneg_right hd
    (show (0 : ℝ) ≤ 2 * (N : ℝ) ^ 2 by positivity)
  have hb := max_square_sidon_real_modular_bound N Q
  have hsq : ((Real.sqrt (3 / 4) : ℝ) ^ k) ^ 2 = (3 / 4 : ℝ) ^ k := by
    rw [← pow_mul, mul_comm k 2, pow_mul, Real.sq_sqrt (by norm_num)]
  apply (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mp
  nlinarith

lemma square_sidon_primorial_parametric_upper (n N : ℕ) (hn : 0 < n)
    (hN : 128 ^ n ≤ N) :
    (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun m : ℕ => m ^ 2)) : ℝ) ≤
      2 * (Real.sqrt (3 / 4) : ℝ) ^ (sievePrimes n).card * N := by
  apply square_sidon_upper_of_modulus _ _ (sievePrimorial n) (sievePrimorial_pos n)
  · calc
      _ ≤ 2 ^ (3 * n) * 4 ^ (2 * n) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by omega)
          ((sievePrimes_card_le n).trans (by omega))) (sievePrimorial_le n)
      _ = 128 ^ n := by rw [pow_mul, pow_mul, ← mul_pow]; norm_num
      _ ≤ N := hN
  · exact sievePrimorial_density n

lemma square_sidon_primorial_upper (N : ℕ) (hN : 128 ^ 128 ≤ N) :
    (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) ≤
      2 * N * Real.exp (-Real.log N / (512 * Real.log (Real.log N))) := by
  let n := Nat.log 128 N
  let k := (sievePrimes n).card
  have hn128 : 128 ≤ n := Nat.le_log_of_pow_le (by omega) hN
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn128R : (128 : ℝ) ≤ n := by exact_mod_cast hn128
  have hNp : 0 < N := (by positivity : 0 < (128 : ℕ) ^ 128).trans_le hN
  have hNpR : (0 : ℝ) < N := by exact_mod_cast hNp
  have hpow : 128 ^ n ≤ N := Nat.pow_log_le_self 128 hNp.ne'
  have hpowR : (128 : ℝ) ^ n ≤ N := by exact_mod_cast hpow
  have hupper : (N : ℝ) ≤ (128 : ℝ) ^ (n + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by omega : 1 < (128 : ℕ)) N).le
  have hlog2lo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hlog2hi : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hlog128 : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  have hlog128lo : 1 ≤ Real.log 128 := by linarith
  have hlog128hi : Real.log 128 ≤ 7 := by linarith
  have hlo : (n : ℝ) ≤ Real.log N := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 128 ^ n) hpowR
    rw [Real.log_pow] at h
    nlinarith
  have hhi : Real.log N ≤ 8 * n := by
    have h := Real.log_le_log hNpR hupper
    rw [Real.log_pow] at h
    push_cast at h
    nlinarith
  have hloglog : 0 < Real.log (Real.log N) :=
    Real.log_pos (by linarith)
  have hlogn : Real.log n ≤ Real.log (Real.log N) := Real.log_le_log hnp hlo
  have hk : Real.log N ≤ 64 * k * Real.log (Real.log N) := by
    have hc := sievePrimes_card_log_lower n hn128
    change (n : ℝ) / 8 ≤ (k : ℝ) * Real.log n at hc
    have ht := mul_le_mul_of_nonneg_left hlogn (Nat.cast_nonneg (α := ℝ) k)
    nlinarith
  have hquot : Real.log N / (512 * Real.log (Real.log N)) ≤ (k : ℝ) / 8 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hrlog : Real.log (Real.sqrt (3 / 4)) ≤ -(1 / 8 : ℝ) := by
    rw [Real.log_sqrt (by norm_num)]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
    linarith
  have hrpow : (Real.sqrt (3 / 4) : ℝ) ^ k ≤ Real.exp (-(k : ℝ) / 8) := by
    calc
      _ = Real.exp ((k : ℝ) * Real.log (Real.sqrt (3 / 4))) := by
        rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have h := mul_le_mul_of_nonneg_left hrlog (Nat.cast_nonneg (α := ℝ) k)
        linarith)
  have he : Real.exp (-(k : ℝ) / 8) ≤
      Real.exp (-Real.log N / (512 * Real.log (Real.log N))) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hquot
  have hm := square_sidon_primorial_parametric_upper n N (by omega) hpow
  calc
    _ ≤ 2 * (Real.sqrt (3 / 4) : ℝ) ^ k * N := hm
    _ ≤ 2 * N * Real.exp (-Real.log N / (512 * Real.log (Real.log N))) := by
      have h := mul_le_mul_of_nonneg_left (hrpow.trans he)
        (show (0 : ℝ) ≤ 2 * N by positivity)
      nlinarith

#print axioms square_sidon_primorial_upper

end Erdos773
