import Submission.ElementarySquareSieve

/-!
A quantitative modular upper bound. It remains compatible with Erdős 773:
the resulting exponent loss tends to zero.
-/

namespace Erdos773
open Finset

noncomputable def dyadicSievePrime (i : ℕ) : ℕ :=
  (Nat.exists_prime_lt_and_le_two_mul (2 ^ (i + 2)) (by positivity)).choose

lemma dyadicSievePrime_spec (i : ℕ) :
    (dyadicSievePrime i).Prime ∧ 2 ^ (i + 2) < dyadicSievePrime i ∧
      dyadicSievePrime i ≤ 2 ^ (i + 3) := by
  have h := (Nat.exists_prime_lt_and_le_two_mul (2 ^ (i + 2)) (by positivity)).choose_spec
  refine ⟨h.1, h.2.1, ?_⟩
  simpa [dyadicSievePrime, show i + 3 = (i + 2) + 1 by omega, pow_succ, mul_comm]
    using h.2.2

lemma dyadicSievePrime_strictMono : StrictMono dyadicSievePrime := by
  intro i j hij
  exact ((dyadicSievePrime_spec i).2.2.trans
    (Nat.pow_le_pow_right (by omega) (show i + 3 ≤ j + 2 by omega))).trans_lt
      (dyadicSievePrime_spec j).2.1

noncomputable def dyadicSieveModulus (k : ℕ) : ℕ :=
  ∏ i ∈ range k, dyadicSievePrime i

lemma dyadicSieveModulus_pos (k : ℕ) : 0 < dyadicSieveModulus k := by
  exact Finset.prod_pos (fun i hi => (dyadicSievePrime_spec i).1.pos)

lemma dyadicSieveModulus_le (k : ℕ) : dyadicSieveModulus k ≤ 2 ^ (k + 2) ^ 2 := by
  calc
    _ ≤ ∏ i ∈ range k, (2 : ℕ) ^ (k + 2) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i hi
      exact (dyadicSievePrime_spec i).2.2.trans
        (Nat.pow_le_pow_right (by omega) (show i + 3 ≤ k + 2 by simpa using hi))
    _ = 2 ^ ((k + 2) * k) := by simp [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

lemma dyadicSieveModulus_density (k : ℕ) :
    quadraticResidueDensity (dyadicSieveModulus k) ≤ (3 / 4 : ℝ) ^ k := by
  induction k with
  | zero => simpa [dyadicSieveModulus] using quadraticResidueDensity_le_one 1
  | succ k ih =>
    letI : NeZero (dyadicSieveModulus k) := ⟨(dyadicSieveModulus_pos k).ne'⟩
    letI : NeZero (dyadicSievePrime k) := ⟨(dyadicSievePrime_spec k).1.ne_zero⟩
    have hc : (dyadicSieveModulus k).Coprime (dyadicSievePrime k) := by
      apply Nat.Coprime.symm
      apply Nat.Coprime.prod_right
      intro i hi
      apply ((dyadicSievePrime_spec k).1.coprime_iff_not_dvd).mpr
      intro hd
      have he := (Nat.prime_dvd_prime_iff_eq (dyadicSievePrime_spec k).1
        (dyadicSievePrime_spec i).1).mp hd
      exact (Nat.ne_of_gt (dyadicSievePrime_strictMono (mem_range.mp hi))) he
    have hp4 : 4 ≤ dyadicSievePrime k := by
      have hp := (dyadicSievePrime_spec k).2.1
      have h4 : (4 : ℕ) ≤ 2 ^ (k + 2) := by
        simpa using (Nat.pow_le_pow_right (n := 2) (by omega) (show 2 ≤ k + 2 by omega))
      omega
    change quadraticResidueDensity (∏ i ∈ range (k + 1), dyadicSievePrime i) ≤ _
    rw [prod_range_succ]
    calc
      _ ≤ quadraticResidueDensity (dyadicSieveModulus k) *
          quadraticResidueDensity (dyadicSievePrime k) := quadraticResidueDensity_mul_le _ _ hc
      _ ≤ (3 / 4 : ℝ) ^ k * (3 / 4) :=
        mul_le_mul ih (quadraticResidueDensity_le_three_quarters _ hp4)
          (quadraticResidueDensity_nonneg _) (by positivity)
      _ = _ := (pow_succ _ _).symm

lemma square_sidon_quantitative_upper_sq (k N : ℕ) (hN : 2 ^ (k + 3) ^ 2 ≤ N) :
    (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) ^ 2 ≤
      4 * (3 / 4 : ℝ) ^ k * (N : ℝ) ^ 2 := by
  let Q := dyadicSieveModulus k
  letI : NeZero Q := ⟨(dyadicSieveModulus_pos k).ne'⟩
  have hQN : 2 ^ k * Q ≤ N := by
    calc
      _ ≤ 2 ^ k * 2 ^ (k + 2) ^ 2 := Nat.mul_le_mul_left _ (dyadicSieveModulus_le k)
      _ = 2 ^ (k + (k + 2) ^ 2) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (k + 3) ^ 2 := Nat.pow_le_pow_right (by omega) (by nlinarith)
      _ ≤ N := hN
  have hQN' : (2 : ℝ) ^ k * Q ≤ N := by exact_mod_cast hQN
  have hhalf := mul_le_mul_of_nonneg_left hQN' (by positivity : (0 : ℝ) ≤ (1 / 2) ^ k)
  have he : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
  rw [← mul_assoc, he, one_mul] at hhalf
  have hhalf34 : (1 / 2 : ℝ) ^ k ≤ (3 / 4 : ℝ) ^ k := by
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hQr : (Q : ℝ) ≤ (3 / 4 : ℝ) ^ k * N :=
    hhalf.trans (mul_le_mul_of_nonneg_right hhalf34 (Nat.cast_nonneg N))
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast ((Nat.one_le_pow _ _ (by omega : 0 < (2 : ℕ))).trans hN)
  have hs : ((quadraticResidues Q).card : ℝ) ≤ Q := by
    exact_mod_cast (by simpa using card_le_univ (quadraticResidues Q) :
      (quadraticResidues Q).card ≤ Q)
  have ht := mul_le_mul (hs.trans hQr) (show (N : ℝ) + 1 ≤ 2 * N by linarith)
    (by positivity : (0 : ℝ) ≤ N + 1) (by positivity : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ k * N)
  have hd := mul_le_mul_of_nonneg_right (dyadicSieveModulus_density k)
    (show (0 : ℝ) ≤ 2 * (N : ℝ) ^ 2 by positivity)
  have hb := max_square_sidon_real_modular_bound N Q
  change quadraticResidueDensity Q * (2 * (N : ℝ) ^ 2) ≤ _ at hd
  nlinarith

lemma square_sidon_quantitative_upper (k N : ℕ) (hN : 2 ^ (k + 3) ^ 2 ≤ N) :
    (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) ≤
      2 * (Real.sqrt (3 / 4) : ℝ) ^ k * N := by
  have h := square_sidon_quantitative_upper_sq k N hN
  have hs : ((Real.sqrt (3 / 4) : ℝ) ^ k) ^ 2 = (3 / 4 : ℝ) ^ k := by
    rw [← pow_mul, mul_comm k 2, pow_mul, Real.sq_sqrt (by norm_num)]
  apply (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mp
  nlinarith

lemma square_sidon_stretched_exponential_upper (N : ℕ) (hN : 512 ≤ N) :
    (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) ≤
      4 * N * Real.exp (-Real.sqrt (Real.log N) / 8) := by
  let l := Nat.log 2 N
  let t := Nat.sqrt l
  let k := t - 3
  have hNp : 0 < N := by omega
  have hNp' : (0 : ℝ) < N := by exact_mod_cast hNp
  have hl9 : 9 ≤ l := Nat.le_log_of_pow_le (by omega) (by norm_num; exact hN)
  have ht3 : 3 ≤ t := Nat.le_sqrt.mpr (by norm_num; exact hl9)
  have hk : k + 3 = t := Nat.sub_add_cancel ht3
  have ht2 : t ^ 2 ≤ l := by simpa only [pow_two] using Nat.sqrt_le l
  have hpow : 2 ^ (k + 3) ^ 2 ≤ N := by
    rw [hk]
    exact (Nat.pow_le_pow_right (by omega) ht2).trans (Nat.pow_log_le_self 2 hNp.ne')
  have hlupper : l + 1 ≤ (t + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt l
    change l < (t + 1) * (t + 1) at h
    nlinarith
  have hNupper : N ≤ 2 ^ (t + 1) ^ 2 :=
    (Nat.lt_pow_succ_log_self (by omega : 1 < (2 : ℕ)) N).le.trans
      (Nat.pow_le_pow_right (by omega) hlupper)
  have hln : Real.log N ≤ ((t : ℝ) + 1) ^ 2 := by
    have hn : (N : ℝ) ≤ (2 : ℝ) ^ (t + 1) ^ 2 := by exact_mod_cast hNupper
    have h := Real.log_le_log hNp' hn
    rw [Real.log_pow] at h
    have h2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hh := mul_le_mul_of_nonneg_left h2
      (Nat.cast_nonneg (α := ℝ) ((t + 1) ^ 2))
    push_cast at h hh
    nlinarith
  have hsqrt : Real.sqrt (Real.log N) ≤ (k : ℝ) + 4 := by
    have h := (Real.sqrt_le_iff).mpr ⟨by positivity, hln⟩
    have hk' : (k : ℝ) + 3 = t := by exact_mod_cast hk
    linarith
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
      Real.exp (1 / 2) * Real.exp (-Real.sqrt (Real.log N) / 8) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hexp : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    convert Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) using 1 <;> norm_num
  have hfinal : (Real.sqrt (3 / 4) : ℝ) ^ k ≤
      2 * Real.exp (-Real.sqrt (Real.log N) / 8) :=
    hrpow.trans (he.trans (mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg _)))
  have hh := mul_le_mul_of_nonneg_right hfinal (show (0 : ℝ) ≤ 2 * N by positivity)
  have hm := square_sidon_quantitative_upper k N hpow
  nlinarith

#print axioms square_sidon_quantitative_upper
#print axioms square_sidon_stretched_exponential_upper

end Erdos773
