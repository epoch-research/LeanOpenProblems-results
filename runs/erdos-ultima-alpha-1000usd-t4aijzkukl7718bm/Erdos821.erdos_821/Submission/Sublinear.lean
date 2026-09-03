import Submission.Work
import Submission.Sieve

/-!
# A global sublinear bound for inverse-totient multiplicity

Auxiliary development. A sublinear upper bound does not settle Erdős 821.
-/

open Nat Filter
open scoped Classical

namespace Erdos821
open Sieve

lemma card_multiples_Icc_le_div (A d : ℕ) (hd : 0 < d) :
    (((Finset.Icc 1 A).filter (fun n => d ∣ n)).card : ℝ) ≤ (A : ℝ) / d := by
  let E := (Finset.Icc 1 A).filter (fun n => d ∣ n)
  have hcard : E.card ≤ A / d := by
    have h := Finset.card_le_card_of_injOn (s := E) (t := Finset.Icc 1 (A / d))
      (fun n : ℕ => n / d) ?_ ?_
    · simpa only [Nat.card_Icc, Nat.add_sub_cancel] using h
    · intro n hn
      change n ∈ E at hn
      obtain ⟨hnI, hdn⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1, hnA⟩ := Finset.mem_Icc.mp hnI
      exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn1 hdn) hd,
        Nat.div_le_div_right hnA⟩
    · intro n hn m hm h
      change n ∈ E at hn
      change m ∈ E at hm
      have hdn := (Finset.mem_filter.mp hn).2
      have hdm := (Finset.mem_filter.mp hm).2
      change n / d = m / d at h
      rw [← Nat.mul_div_cancel' hdn, ← Nat.mul_div_cancel' hdm, h]
  apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  exact_mod_cast (Nat.mul_le_mul_right d hcard).trans (Nat.div_mul_le_self A d)

lemma average_prime_product_le (A : ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ (A + 1).primesBelow, 0 ≤ w p) :
    (∑ n ∈ Finset.Icc 1 A, ∏ p ∈ n.primeFactors, (1 + w p)) ≤
      (A : ℝ) * ∏ p ∈ (A + 1).primesBelow, (1 + w p / (p : ℝ)) := by
  let Q := (A + 1).primesBelow
  have hQ (p : ℕ) (hp : p ∈ Q) : p.Prime := (Nat.mem_primesBelow.mp hp).2
  have hsub (n : ℕ) (hn : n ∈ Finset.Icc 1 A) : n.primeFactors ⊆ Q := by
    intro p hp
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    have hpn := Nat.le_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)
    exact Nat.mem_primesBelow.mpr ⟨by have := (Finset.mem_Icc.mp hn).2; omega,
      Nat.prime_of_mem_primeFactors hp⟩
  have hexpand (n : ℕ) (hn : n ∈ Finset.Icc 1 A) :
      (∏ p ∈ n.primeFactors, (1 + w p)) =
        ∑ S ∈ Q.powerset, if (∏ p ∈ S, p) ∣ n then ∏ p ∈ S, w p else 0 := by
    have hfilter : Q.powerset.filter (fun S => (∏ p ∈ S, p) ∣ n) = n.primeFactors.powerset := by
      ext S
      constructor
      · intro hS
        obtain ⟨hSQ, hdiv⟩ := Finset.mem_filter.mp hS
        apply Finset.mem_powerset.mpr
        intro p hp
        have hpQ := Finset.mem_powerset.mp hSQ hp
        exact (hQ p hpQ).mem_primeFactors ((Finset.dvd_prod_of_mem id hp).trans hdiv)
          (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
      · intro hS
        have hSn := Finset.mem_powerset.mp hS
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hSn.trans (hsub n hn)), ?_⟩
        exact (prod_primes_dvd_iff S (fun p hp => Nat.prime_of_mem_primeFactors (hSn hp)) n).mpr
          (fun p hp => Nat.dvd_of_mem_primeFactors (hSn hp))
    rw [← Finset.sum_filter, hfilter, ← Finset.prod_one_add]
  have hweight (S : Finset ℕ) (hS : S ∈ Q.powerset) : 0 ≤ ∏ p ∈ S, w p :=
    Finset.prod_nonneg (fun p hp => hw p (Finset.mem_powerset.mp hS hp))
  calc
    (∑ n ∈ Finset.Icc 1 A, ∏ p ∈ n.primeFactors, (1 + w p)) =
        ∑ n ∈ Finset.Icc 1 A, ∑ S ∈ Q.powerset,
          if (∏ p ∈ S, p) ∣ n then ∏ p ∈ S, w p else 0 := by
      apply Finset.sum_congr rfl
      exact hexpand
    _ = ∑ S ∈ Q.powerset, (∏ p ∈ S, w p) *
        (((Finset.Icc 1 A).filter (fun n => (∏ p ∈ S, p) ∣ n)).card : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S hS
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ S ∈ Q.powerset, (∏ p ∈ S, w p) * ((A : ℝ) / (∏ p ∈ S, p : ℕ)) := by
      apply Finset.sum_le_sum
      intro S hS
      apply mul_le_mul_of_nonneg_left _ (hweight S hS)
      exact card_multiples_Icc_le_div A _
        (Finset.prod_pos (fun p hp => (hQ p (Finset.mem_powerset.mp hS hp)).pos))
    _ = (A : ℝ) * ∑ S ∈ Q.powerset, ∏ p ∈ S, w p / (p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.prod_div_distrib, Nat.cast_prod]
      ring
    _ = _ := by rw [← Finset.prod_one_add]

lemma totient_ratio_average (A : ℕ) :
    (∑ n ∈ Finset.Icc 1 A, ((n : ℝ) / Nat.totient n) ^ 2) ≤
      totientRatioAverageConstant * (A : ℝ) := by
  let w : ℕ → ℝ := fun p => ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 - 1
  let Q := (A + 1).primesBelow
  have hw (p : ℕ) (hp : p.Prime) : 0 ≤ w p ∧ w p ≤ 8 / (p : ℝ) := by
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hpm1 : 0 < (p : ℝ) - 1 := by linarith
    have hge : (1 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := (one_le_div hpm1).mpr (by linarith)
    refine ⟨by dsimp [w]; nlinarith, ?_⟩
    have heq : w p = (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 := by
      dsimp [w]
      field_simp
      ring
    rw [heq]
    apply (div_le_div_iff₀ (sq_pos_of_pos hpm1) hp0).mpr
    nlinarith [sq_nonneg ((p : ℝ) - 2)]
  have hseries : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by decide)
  have hsum : (∑ p ∈ Q, w p / (p : ℝ)) ≤ 8 * ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := by
    calc
      (∑ p ∈ Q, w p / (p : ℝ)) ≤ ∑ p ∈ Q, 8 * ((p : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        have h := div_le_div_of_nonneg_right (hw p (Nat.mem_primesBelow.mp hp).2).2 (Nat.cast_nonneg p)
        convert h using 1 <;> ring
      _ = 8 * ∑ p ∈ Q, ((p : ℝ) ^ 2)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Summable.sum_le_tsum _ (fun p _ => by positivity) hseries) (by norm_num)
  have hprod : (∏ p ∈ Q, (1 + w p / (p : ℝ))) ≤ totientRatioAverageConstant := by
    calc
      _ ≤ ∏ p ∈ Q, Real.exp (w p / (p : ℝ)) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact add_nonneg zero_le_one (div_nonneg (hw p (Nat.mem_primesBelow.mp hp).2).1
            (Nat.cast_nonneg p))
        · intro p hp
          simpa only [add_comm] using Real.add_one_le_exp (w p / (p : ℝ))
      _ = Real.exp (∑ p ∈ Q, w p / (p : ℝ)) := (Real.exp_sum _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsum
  have havg := average_prime_product_le A w
    (fun p hp => (hw p (Nat.mem_primesBelow.mp hp).2).1)
  have heq (n : ℕ) (hn : n ∈ Finset.Icc 1 A) :
      ((n : ℝ) / Nat.totient n) ^ 2 = ∏ p ∈ n.primeFactors, (1 + w p) := by
    rw [totient_ratio_eq_prime_product n (Finset.mem_Icc.mp hn).1, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro p hp
    dsimp [w]
    ring
  have hH : 0 ≤ (A : ℝ) := Nat.cast_nonneg A
  calc
    (∑ n ∈ Finset.Icc 1 A, ((n : ℝ) / Nat.totient n) ^ 2) =
        ∑ n ∈ Finset.Icc 1 A, (∏ p ∈ n.primeFactors, (1 + w p)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [heq n hn]
    _ ≤ (A : ℝ) * ∏ p ∈ Q, (1 + w p / (p : ℝ)) := havg
    _ ≤ (A : ℝ) * totientRatioAverageConstant := mul_le_mul_of_nonneg_left hprod hH
    _ = _ := mul_comm _ _


lemma totient_fiber_block_card_le (S : Finset ℕ) (n M : ℕ)
    (hn : 0 < n) (hM : 0 < M)
    (hS : ∀ m ∈ S, M ≤ m ∧ m ≤ 2 * M ∧ Nat.totient m = n) :
    (S.card : ℝ) ≤ 2 * totientRatioAverageConstant * (n : ℝ) ^ 2 / M := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hsub : S ⊆ Finset.Icc 1 (2 * M) := by
    intro m hm
    exact Finset.mem_Icc.mpr ⟨hM.trans_le (hS m hm).1, (hS m hm).2.1⟩
  have hsum : (∑ m ∈ S, ((m : ℝ) / Nat.totient m) ^ 2) ≤
      totientRatioAverageConstant * (2 * M) := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => sq_nonneg _)).trans
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using totient_ratio_average (2 * M))
  have hsq : (S.card : ℝ) * (M : ℝ) ^ 2 ≤
      2 * totientRatioAverageConstant * (M : ℝ) * (n : ℝ) ^ 2 := by
    calc
      (S.card : ℝ) * (M : ℝ) ^ 2 = ∑ _m ∈ S, (M : ℝ) ^ 2 := by simp
      _ ≤ ∑ m ∈ S, (m : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro m hm
        exact pow_le_pow_left₀ hMR.le (by exact_mod_cast (hS m hm).1) 2
      _ = (n : ℝ) ^ 2 * ∑ m ∈ S, ((m : ℝ) / Nat.totient m) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        rw [(hS m hm).2.2]
        field_simp
      _ ≤ (n : ℝ) ^ 2 * (totientRatioAverageConstant * (2 * M)) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = _ := by ring
  apply (le_div_iff₀ hMR).mpr
  apply (mul_le_mul_iff_right₀ hMR).mp
  nlinarith

lemma totient_fiber_tail_card_le (S : Finset ℕ) (n B : ℕ)
    (hn : 0 < n) (hB : 0 < B)
    (hS : ∀ m ∈ S, B ≤ m ∧ Nat.totient m = n) :
    (S.card : ℝ) ≤ 4 * totientRatioAverageConstant * (n : ℝ) ^ 2 / B := by
  let j : ℕ → ℕ := fun m => Nat.log 2 (m / B)
  have hblock (i : ℕ) :
      ((S.filter (fun m => j m = i)).card : ℝ) ≤
        (2 * totientRatioAverageConstant * (n : ℝ) ^ 2 / B) * (1 / 2 : ℝ) ^ i := by
    have h := totient_fiber_block_card_le (S.filter (fun m => j m = i)) n (2 ^ i * B)
      hn (Nat.mul_pos (by positivity) hB) ?_
    · convert h using 1
      push_cast
      simp only [div_eq_mul_inv, mul_inv, inv_pow, one_mul]
      ring
    · intro m hm
      obtain ⟨hmS, hi⟩ := Finset.mem_filter.mp hm
      have hmB := (hS m hmS).1
      have hdiv : 0 < m / B := Nat.div_pos hmB hB
      have hlo := Nat.pow_log_le_self 2 hdiv.ne'
      have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (m / B)
      change Nat.log 2 (m / B) = i at hi
      rw [hi] at hlo hhi
      refine ⟨(Nat.mul_le_mul_right B hlo).trans (Nat.div_mul_le_self m B), ?_, (hS m hmS).2⟩
      have hmhi : m < 2 ^ (i + 1) * B := (Nat.div_lt_iff_lt_mul hB).mp hhi
      rw [pow_succ] at hmhi
      nlinarith
  have hcard : (S.card : ℝ) = ∑ i ∈ S.image j, ((S.filter (fun m => j m = i)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (s := S) (t := S.image j)
      (fun m hm => Finset.mem_image_of_mem j hm)
  have hgeom : (∑ i ∈ S.image j, (1 / 2 : ℝ) ^ i) ≤ 2 := by
    have hsum := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    have hle := hsum.summable.sum_le_tsum (S.image j) (fun i _ => by positivity)
    rw [hsum.tsum_eq] at hle
    norm_num at hle
    exact hle
  have hC : 0 ≤ totientRatioAverageConstant := (Real.exp_pos _).le
  calc
    (S.card : ℝ) = _ := hcard
    _ ≤ ∑ i ∈ S.image j,
        (2 * totientRatioAverageConstant * (n : ℝ) ^ 2 / B) * (1 / 2 : ℝ) ^ i :=
      Finset.sum_le_sum (fun i _ => hblock i)
    _ = (2 * totientRatioAverageConstant * (n : ℝ) ^ 2 / B) *
        ∑ i ∈ S.image j, (1 / 2 : ℝ) ^ i := (Finset.mul_sum _ _ _).symm
    _ ≤ (2 * totientRatioAverageConstant * (n : ℝ) ^ 2 / B) * 2 := by gcongr
    _ = _ := by ring

lemma sum_Icc_inv_sq_le (y M : ℕ) (hy : 0 < y) :
    (∑ d ∈ Finset.Icc y M, ((d : ℝ) ^ 2)⁻¹) ≤ 2 / y := by
  by_cases hyM : y ≤ M
  · have hI : Finset.Icc y M = Finset.Ico y (M + 1) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    have htel := Finset.sum_Ico_sub (fun d : ℕ => -(d : ℝ)⁻¹)
      (show y ≤ M + 1 by omega)
    simp only [neg_sub_neg] at htel
    have htel' : (∑ d ∈ Finset.Icc y M, ((d : ℝ)⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹)) =
        (y : ℝ)⁻¹ - ((M + 1 : ℕ) : ℝ)⁻¹ := by rw [hI]; exact htel
    calc
      _ ≤ ∑ d ∈ Finset.Icc y M, 2 * ((d : ℝ)⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hy.trans_le (Finset.mem_Icc.mp hd).1
        have hd0 : (0 : ℝ) < d := by linarith
        have heq : (d : ℝ)⁻¹ - ((d + 1 : ℕ) : ℝ)⁻¹ = 1 / ((d : ℝ) * (d + 1)) := by
          push_cast
          field_simp
          ring
        rw [heq, ← one_div, mul_one_div]
        apply (div_le_div_iff₀ (sq_pos_of_pos hd0) (mul_pos hd0 (by linarith))).mpr
        nlinarith
      _ = 2 * ((y : ℝ)⁻¹ - ((M + 1 : ℕ) : ℝ)⁻¹) := by rw [← Finset.mul_sum, htel']
      _ ≤ _ := by
        rw [div_eq_mul_inv]
        have hInv : 0 ≤ (((M + 1 : ℕ) : ℝ))⁻¹ := by positivity
        linarith
  · rw [Finset.Icc_eq_empty_of_lt (Nat.lt_of_not_ge hyM), Finset.sum_empty]
    positivity

lemma card_large_square_divisor_le (S : Finset ℕ) (M y : ℕ) (hy : 0 < y)
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ M ∧ ∃ d : ℕ, y ≤ d ∧ d ^ 2 ∣ m) :
    (S.card : ℝ) ≤ 2 * (M : ℝ) / y := by
  let F : ℕ → Finset ℕ := fun d => (Finset.Icc 1 M).filter (fun m => d ^ 2 ∣ m)
  have hsub : S ⊆ (Finset.Icc y M).biUnion F := by
    intro m hm
    obtain ⟨hm0, hmM, d, hyd, hdm⟩ := hS m hm
    have hdM : d ≤ M := (Nat.le_self_pow (by decide : 2 ≠ 0) d).trans
      ((Nat.le_of_dvd hm0 hdm).trans hmM)
    exact Finset.mem_biUnion.mpr ⟨d, Finset.mem_Icc.mpr ⟨hyd, hdM⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm0, hmM⟩, hdm⟩⟩
  have hcard : S.card ≤ ∑ d ∈ Finset.Icc y M, (F d).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc
    (S.card : ℝ) ≤ ∑ d ∈ Finset.Icc y M, ((F d).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ d ∈ Finset.Icc y M, (M : ℝ) * ((d : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro d hd
      have hd0 : 0 < d := hy.trans_le (Finset.mem_Icc.mp hd).1
      have h := card_multiples_Icc_le_div M (d ^ 2) (by positivity)
      push_cast at h
      simpa only [F, div_eq_mul_inv] using h
    _ = (M : ℝ) * ∑ d ∈ Finset.Icc y M, ((d : ℝ) ^ 2)⁻¹ := (Finset.mul_sum _ _ _).symm
    _ ≤ (M : ℝ) * (2 / y) := mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le y M hy) (Nat.cast_nonneg M)
    _ = _ := by ring

lemma card_fiber_large_prime_once_le (S : Finset ℕ) (n M y : ℕ) (hy : 0 < y)
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ M ∧ Nat.totient m = n ∧
      ∃ p : ℕ, p.Prime ∧ y ≤ p ∧ p ∣ m ∧ ¬p ^ 2 ∣ m) :
    (S.card : ℝ) ≤ (M : ℝ) / y := by
  let f : ℕ → ℕ := fun a => a * (n / Nat.totient a + 1)
  have hcover : S ⊆ (Finset.Icc 1 (M / y)).image f := by
    intro m hm
    obtain ⟨hm0, hmM, hphi, p, hp, hyp, hpm, hp2m⟩ := hS m hm
    let a := m / p
    have ha0 : 0 < a := Nat.div_pos (Nat.le_of_dvd hm0 hpm) hp.pos
    have hmap : a ≤ M / y := by
      apply (Nat.le_div_iff_mul_le hy).mpr
      exact (Nat.mul_le_mul_left a hyp).trans (by simpa only [a, Nat.div_mul_cancel hpm] using hmM)
    have hap : p.Coprime a := hp.coprime_iff_not_dvd.mpr (by
      intro h
      apply hp2m
      simpa only [pow_two] using (Nat.dvd_div_iff_mul_dvd hpm).mp h)
    have hphi' : Nat.totient a * (p - 1) = n := by
      rw [← Nat.totient_prime hp, ← Nat.totient_mul hap.symm]
      simpa only [a, Nat.div_mul_cancel hpm] using hphi
    have hpval : n / Nat.totient a + 1 = p := by
      rw [← hphi', Nat.mul_div_cancel_left _ (Nat.totient_pos.mpr ha0)]
      have := hp.two_le
      omega
    exact Finset.mem_image.mpr ⟨a, Finset.mem_Icc.mpr ⟨ha0, hmap⟩, by
      dsimp [f]
      rw [hpval]
      exact Nat.div_mul_cancel hpm⟩
  have hcard : S.card ≤ M / y := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using
      (Finset.card_le_card hcover).trans (Finset.card_image_le)
  apply (le_div_iff₀ (by exact_mod_cast hy : (0 : ℝ) < y)).mpr
  exact_mod_cast (Nat.mul_le_mul_right y hcard).trans (Nat.div_mul_le_self M y)

lemma bounded_totient_fiber_card_le (S : Finset ℕ) (n M y : ℕ) (hy : 0 < y)
    (hS : ∀ m ∈ S, 0 < m ∧ m ≤ M ∧ Nat.totient m = n) :
    (S.card : ℝ) ≤ 3 * (M : ℝ) / y + (2 ^ y.primesBelow.card : ℝ) * Nat.sqrt M := by
  let A := S.filter (fun m => m ∈ Nat.smoothNumbers y)
  let B := S.filter (fun m => ∃ d : ℕ, y ≤ d ∧ d ^ 2 ∣ m)
  let D := S.filter (fun m => ∃ p : ℕ, p.Prime ∧ y ≤ p ∧ p ∣ m ∧ ¬p ^ 2 ∣ m)
  have hsub : S ⊆ A ∪ (B ∪ D) := by
    intro m hm
    by_cases hsm : m ∈ Nat.smoothNumbers y
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm, hsm⟩)
    · have hnot : ¬∀ p : ℕ, p.Prime → p ∣ m → p < y := by
        simpa only [Nat.mem_smoothNumbers'] using hsm
      push_neg at hnot
      obtain ⟨p, hp, hpm, hyp⟩ := hnot
      apply Finset.mem_union_right
      by_cases hp2m : p ^ 2 ∣ m
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm, p, hyp, hp2m⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm, p, hp, hyp, hpm, hp2m⟩)
  have hA : A.card ≤ 2 ^ y.primesBelow.card * Nat.sqrt M := by
    apply (Finset.card_le_card (t := Nat.smoothNumbersUpTo M y) ?_).trans (Nat.smoothNumbersUpTo_card_le M y)
    intro m hm
    obtain ⟨hmS, hmSm⟩ := Finset.mem_filter.mp hm
    exact Nat.mem_smoothNumbersUpTo.mpr ⟨(hS m hmS).2.1, hmSm⟩
  have hB : (B.card : ℝ) ≤ 2 * (M : ℝ) / y := by
    apply card_large_square_divisor_le B M y hy
    intro m hm
    obtain ⟨hmS, hmD⟩ := Finset.mem_filter.mp hm
    exact ⟨(hS m hmS).1, (hS m hmS).2.1, hmD⟩
  have hD : (D.card : ℝ) ≤ (M : ℝ) / y := by
    apply card_fiber_large_prime_once_le D n M y hy
    intro m hm
    obtain ⟨hmS, hmD⟩ := Finset.mem_filter.mp hm
    exact ⟨(hS m hmS).1, (hS m hmS).2.1, (hS m hmS).2.2, hmD⟩
  have hcard : S.card ≤ A.card + (B.card + D.card) :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_union_le _ _) _))
  have hcardR : (S.card : ℝ) ≤ (A.card : ℝ) + (B.card + D.card) := by exact_mod_cast hcard
  have hAR : (A.card : ℝ) ≤ (2 ^ y.primesBelow.card : ℝ) * Nat.sqrt M := by exact_mod_cast hA
  calc
    (S.card : ℝ) ≤ (A.card : ℝ) + (B.card + D.card) := hcardR
    _ ≤ (2 ^ y.primesBelow.card : ℝ) * Nat.sqrt M + (2 * (M : ℝ) / y + M / y) :=
      add_le_add hAR (add_le_add hB hD)
    _ = _ := by ring

lemma g_le_linear_coeff_sqrt (n A y : ℕ) (hn : 0 < n) (hA : 0 < A) (hy : 0 < y) :
    (g n : ℝ) ≤ (4 * totientRatioAverageConstant / A + 3 * (A : ℝ) / y) * n +
      (2 ^ y.primesBelow.card : ℝ) * Nat.sqrt (A * n) := by
  let S := (finite_totient_fiber n).toFinset
  let L := S.filter (fun m => m ≤ A * n)
  let H := S.filter (fun m => ¬m ≤ A * n)
  have hphi : ∀ m ∈ S, Nat.totient m = n := fun m hm => (finite_totient_fiber n).mem_toFinset.mp hm
  have hL := bounded_totient_fiber_card_le L n (A * n) y hy (by
    intro m hm
    obtain ⟨hmS, hmB⟩ := Finset.mem_filter.mp hm
    refine ⟨Nat.totient_pos.mp ?_, hmB, hphi m hmS⟩
    rwa [hphi m hmS])
  have hH := totient_fiber_tail_card_le H n (A * n) hn (Nat.mul_pos hA hn) (by
    intro m hm
    obtain ⟨hmS, hmB⟩ := Finset.mem_filter.mp hm
    exact ⟨by omega, hphi m hmS⟩)
  have hsub : S ⊆ L ∪ H := by
    intro m hm
    by_cases h : m ≤ A * n
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm, h⟩)
  have hcard : S.card ≤ L.card + H.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hScard : S.card = g n := (Set.ncard_eq_toFinset_card _ (finite_totient_fiber n)).symm
  rw [hScard] at hcard
  have hcardR : (g n : ℝ) ≤ (L.card : ℝ) + H.card := by exact_mod_cast hcard
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hAR : (A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  calc
    (g n : ℝ) ≤ (3 * ((A * n : ℕ) : ℝ) / y + (2 ^ y.primesBelow.card : ℝ) * Nat.sqrt (A * n)) +
        4 * totientRatioAverageConstant * (n : ℝ) ^ 2 / ((A * n : ℕ) : ℝ) :=
      hcardR.trans (add_le_add hL hH)
    _ = _ := by push_cast; field_simp; ring

lemma eventually_const_mul_sqrt_mul_le (A : ℕ) (D η : ℝ) (hD : 0 ≤ D) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, D * (Nat.sqrt (A * n) : ℝ) ≤ η * n := by
  obtain ⟨N, hN⟩ := exists_nat_gt (D ^ 2 * A / η ^ 2)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hconst : D ^ 2 * A ≤ (n : ℝ) * η ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hη)).mp (hN.le.trans (by exact_mod_cast hn))
  have hsqrt : (Nat.sqrt (A * n) : ℝ) ^ 2 ≤ (A : ℝ) * n := by
    exact_mod_cast Nat.sqrt_le' (A * n)
  have h1 := mul_le_mul_of_nonneg_left hsqrt (sq_nonneg D)
  have h2 := mul_le_mul_of_nonneg_right hconst (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  apply (sq_le_sq₀ (mul_nonneg hD (Nat.cast_nonneg _)) (mul_nonneg hη.le (Nat.cast_nonneg n))).mp
  nlinarith

/-- The inverse-totient multiplicity is globally sublinear. This is compatible
with the conjectured lower bounds `n^(1-ε)` for every fixed positive `ε`. -/
theorem eventually_g_le_mul (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ ε * n := by
  let C := totientRatioAverageConstant
  have hC : 0 < C := Real.exp_pos _
  obtain ⟨A, hA⟩ := exists_nat_gt (12 * C / ε + 1)
  have hAR : (0 : ℝ) < A := by have := div_pos (mul_pos (by norm_num : (0 : ℝ) < 12) hC) hε; linarith
  have hAN : 0 < A := by exact_mod_cast hAR
  have hAc : 4 * C / A ≤ ε / 3 := by
    apply (div_le_iff₀ hAR).mpr
    have h := (div_lt_iff₀ hε).mp (show 12 * C / ε < A by linarith)
    nlinarith
  obtain ⟨y, hy⟩ := exists_nat_gt (9 * (A : ℝ) / ε + 1)
  have hyR : (0 : ℝ) < y := by have := div_pos (mul_pos (by norm_num : (0 : ℝ) < 9) hAR) hε; linarith
  have hyN : 0 < y := by exact_mod_cast hyR
  have hyc : 3 * (A : ℝ) / y ≤ ε / 3 := by
    apply (div_le_iff₀ hyR).mpr
    have h := (div_lt_iff₀ hε).mp (show 9 * (A : ℝ) / ε < y by linarith)
    nlinarith
  filter_upwards [eventually_const_mul_sqrt_mul_le A (2 ^ y.primesBelow.card) (ε / 3)
      (by positivity) (by positivity), eventually_ge_atTop 1] with n hnS hn
  have hg := g_le_linear_coeff_sqrt n A y (by omega) hAN hyN
  have hc := mul_le_mul_of_nonneg_right (add_le_add hAc hyc) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  change (4 * totientRatioAverageConstant / (A : ℝ) + 3 * (A : ℝ) / y) * n ≤ (ε / 3 + ε / 3) * n at hc
  linarith

theorem g_isLittleO_id :
    (fun n : ℕ => (g n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  simpa only [Real.norm_natCast] using eventually_g_le_mul ε hε

theorem tendsto_g_div_self :
    Tendsto (fun n : ℕ => (g n : ℝ) / n) atTop (nhds 0) :=
  g_isLittleO_id.tendsto_div_nhds_zero

theorem eventually_g_lt_self : ∀ᶠ n : ℕ in atTop, g n < n := by
  filter_upwards [eventually_g_le_mul (1 / 2) (by norm_num), eventually_ge_atTop 1]
    with n hg hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlt : (g n : ℝ) < n := by linarith
  exact_mod_cast hlt

/-- A quantitative version of sublinearity, with an explicit threshold in the
integer parameter `k`. It gives a logarithmic saving, not a fixed power saving. -/
theorem g_le_div_of_two_pow_sq_le (n k : ℕ) (hk : 2 ≤ k)
    (hn : 2 ^ (4 * k ^ 2) ≤ n) :
    (g n : ℝ) ≤ (4 * totientRatioAverageConstant + 4) * n / k := by
  have hkpos : 0 < k := by omega
  have hnpos : 0 < n := (by positivity : 0 < 2 ^ (4 * k ^ 2)).trans_le hn
  let D : ℕ := 2 ^ (k ^ 2).primesBelow.card
  have hpr : (k ^ 2).primesBelow.card ≤ k ^ 2 := by
    simpa only [Nat.primesBelow, Finset.card_range] using
      Finset.card_filter_le (s := Finset.range (k ^ 2)) (p := Nat.Prime)
  have hD : D ^ 2 ≤ 2 ^ (2 * k ^ 2) := by
    calc
      D ^ 2 ≤ (2 ^ (k ^ 2)) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) hpr) 2
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have hk3 : k ^ 3 ≤ 2 ^ (2 * k ^ 2) := by
    calc
      k ^ 3 ≤ (2 ^ k) ^ 3 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 3
      _ = 2 ^ (k * 3) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hbudget : D ^ 2 * k ^ 3 ≤ n := by
    calc
      _ ≤ 2 ^ (2 * k ^ 2) * 2 ^ (2 * k ^ 2) := Nat.mul_le_mul hD hk3
      _ = 2 ^ (4 * k ^ 2) := by rw [← pow_add]; congr 1; ring
      _ ≤ n := hn
  have hsquare : (D * Nat.sqrt (k * n) * k) ^ 2 ≤ n ^ 2 := by
    calc
      _ = D ^ 2 * k ^ 2 * (Nat.sqrt (k * n)) ^ 2 := by ring
      _ ≤ D ^ 2 * k ^ 2 * (k * n) := Nat.mul_le_mul_left _ (Nat.sqrt_le' (k * n))
      _ = D ^ 2 * k ^ 3 * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n hbudget
      _ = n ^ 2 := (pow_two n).symm
  have hsmall : D * Nat.sqrt (k * n) * k ≤ n := by nlinarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hsmallR : (2 ^ (k ^ 2).primesBelow.card : ℝ) * Nat.sqrt (k * n) ≤ (n : ℝ) / k := by
    apply (le_div_iff₀ hkR).mpr
    exact_mod_cast hsmall
  calc
    (g n : ℝ) ≤ (4 * totientRatioAverageConstant / k + 3 * (k : ℝ) / (k ^ 2 : ℕ)) * n +
        (2 ^ (k ^ 2).primesBelow.card : ℝ) * Nat.sqrt (k * n) :=
      g_le_linear_coeff_sqrt n k (k ^ 2) hnpos hkpos (by positivity)
    _ ≤ (4 * totientRatioAverageConstant / k + 3 * (k : ℝ) / (k ^ 2 : ℕ)) * n + (n : ℝ) / k :=
      add_le_add_right hsmallR _
    _ = _ := by push_cast; field_simp; ring

#print axioms totient_ratio_average
#print axioms totient_fiber_tail_card_le
#print axioms bounded_totient_fiber_card_le
#print axioms eventually_g_le_mul
#print axioms g_isLittleO_id
#print axioms tendsto_g_div_self
#print axioms eventually_g_lt_self
#print axioms g_le_div_of_two_pow_sq_le

end Erdos821
