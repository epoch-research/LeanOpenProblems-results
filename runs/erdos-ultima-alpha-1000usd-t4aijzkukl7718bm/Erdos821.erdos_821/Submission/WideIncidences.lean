import Submission.WideDistribution
import Submission.MomentSmoothTransfer

/-!
# Uniform incidence bounds for the wide modulus family

Both primes and proper prime powers have at most sixteen incident moduli.
This prevents a factor equal to the size of the modulus family in the
prime-power remainder.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma wide_prime_divisor_card_le (m n : ℕ) (hm : 1 ≤ m) (hn : 0 < n)
    (hN : n < progressionScaleN (40020*m)) :
    (((wideLeftPool m ∪ wideRightPool m).filter (fun p => p ∣ n)).card) ≤ 4 := by
  let S := (wideLeftPool m ∪ wideRightPool m).filter (fun p => p ∣ n)
  have hsub : S ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨hp,hd⟩ := mem_filter.mp hp
    have hprime : p.Prime := by
      rcases mem_union.mp hp with hp | hp
      · exact wideLeftPool_prime m p hp
      · exact wideRightPool_prime m p hp
    exact Nat.mem_primeFactors.mpr ⟨hprime,hd,hn.ne'⟩
  have hprod : (∏ p ∈ S, p) ≤ n := Nat.le_of_dvd hn
    ((Finset.prod_dvd_prod_of_subset S n.primeFactors (fun p => p) hsub).trans (Nat.prod_primeFactors_dvd n))
  have hlow : (progressionScaleN (10000*m))^S.card ≤ ∏ p ∈ S, p := by
    rw [← prod_const]
    apply Finset.prod_le_prod'
    intro p hp
    exact (widePrimePools_bounds m p (mem_union.mp (mem_filter.mp hp).1)).2.1
  by_contra hc
  have hc5 : 5 ≤ S.card := by change ¬S.card ≤ 4 at hc; omega
  have hp5 := Nat.pow_le_pow_right (by unfold progressionScaleN; positivity : 0 < progressionScaleN (10000*m)) hc5
  have hbig : progressionScaleN (40020*m) < (progressionScaleN (10000*m))^5 := by
    simp only [progressionScaleN, ← pow_mul]
    apply Nat.pow_lt_pow_right (by decide)
    omega
  exact (not_lt_of_ge (hp5.trans (hlow.trans hprod))) (hN.trans hbig)

lemma wide_divisor_incidence_le (m n : ℕ) (hm : 1 ≤ m) (hn : 0 < n)
    (hN : n < progressionScaleN (40020*m)) :
    ((wideProductPool m).filter (fun d => d ∣ n)).card ≤ 16 := by
  let S := (wideLeftPool m ∪ wideRightPool m).filter (fun p => p ∣ n)
  have hS : S.card ≤ 4 := wide_prime_divisor_card_le m n hm hn hN
  have hsub : (wideProductPool m).filter (fun d => d ∣ n) ⊆
      (S ×ˢ S).image (fun z => z.1*z.2) := by
    intro d hd
    obtain ⟨hd,hdn⟩ := mem_filter.mp hd
    obtain ⟨⟨p,q⟩, hpq, rfl⟩ := mem_image.mp hd
    obtain ⟨hp,hq⟩ := mem_product.mp hpq
    have hpS : p ∈ S := mem_filter.mpr ⟨mem_union_left _ hp,(dvd_mul_right p q).trans hdn⟩
    have hqS : q ∈ S := mem_filter.mpr ⟨mem_union_right _ hq,(dvd_mul_left q p).trans hdn⟩
    exact mem_image.mpr ⟨(p,q),mem_product.mpr ⟨hpS,hqS⟩,rfl⟩
  calc
    _ ≤ ((S ×ˢ S).image (fun z => z.1*z.2)).card := card_le_card hsub
    _ ≤ (S ×ˢ S).card := card_image_le
    _ = S.card*S.card := card_product _ _
    _ ≤ 16 := Nat.mul_le_mul hS hS

lemma sum_family_progressions_eq_incidence (M : Finset ℕ) (N : ℕ) :
    (∑ d ∈ M, residueOneMangoldt d N) =
      ∑ n ∈ Icc 1 N, ((M.filter (fun d => d ∣ n-1)).card : ℝ)*vonMangoldt n := by
  simp only [residueOneMangoldt]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  simp only [residue_one_iff_dvd_pred (mem_Icc.mp hn).1]
  rw [← sum_filter, sum_const, nsmul_eq_mul]

lemma sum_rough_family_counts_eq_incidence (M : Finset ℕ) (N Y : ℕ) :
    (∑ d ∈ M, ((roughProgressionPrimes d Y N).card : ℝ)) =
      ∑ n ∈ Icc 1 N, if n.Prime ∧ n-1 ∉ Nat.smoothNumbers Y then
        ((M.filter (fun d => d ∣ n-1)).card : ℝ) else 0 := by
  have hset (d : ℕ) : roughProgressionPrimes d Y N =
      (Icc 1 N).filter (fun n => n.Prime ∧ n-1 ∉ Nat.smoothNumbers Y ∧ d ∣ n-1) := by
    ext n
    simp only [roughProgressionPrimes,mem_filter,Nat.mem_primesBelow,mem_Icc]
    constructor
    · rintro ⟨⟨hnN,hp⟩,hd,hs⟩
      exact ⟨⟨hp.pos,by omega⟩,hp,hs,hd⟩
    · rintro ⟨⟨hn,hnN⟩,hp,hs,hd⟩
      exact ⟨⟨by omega,hp⟩,hd,hs⟩
  simp only [hset,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  by_cases h : n.Prime ∧ n-1 ∉ Nat.smoothNumbers Y
  · simp only [h.1,h.2,true_and,not_false_eq_true,if_true]
  · have h' : ∀ d, ¬(n.Prime ∧ n-1 ∉ Nat.smoothNumbers Y ∧ d ∣ n-1) :=
      fun _ hd => h ⟨hd.1,hd.2.1⟩
    simp only [if_neg h,if_neg (h' _),sum_const_zero]

/-- The rough incidence term is not multiplied by the survivor overcount. -/
theorem family_progression_weight_le_smooth_count (M : Finset ℕ) (N Y C : ℕ)
    (hN : 1 ≤ N) (hI : ∀ n, 0 < n → n < N → (M.filter (fun d => d ∣ n)).card ≤ C) :
    (∑ d ∈ M, residueOneMangoldt d N) ≤ Real.log N*
      ((C : ℝ)*((smoothPrimePool N Y).card : ℝ) +
       (∑ d ∈ M, ((roughProgressionPrimes d Y N).card : ℝ)) + 2*C*Real.sqrt N) := by
  let G := smoothPrimePool N Y
  let I (n : ℕ) : ℕ := (M.filter (fun d => d ∣ n-1)).card
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg _
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      (I n : ℝ)*vonMangoldt n ≤
        (if n ∈ G then (C : ℝ)*Real.log N else 0) +
        (if n.Prime ∧ n-1 ∉ Nat.smoothNumbers Y then (I n : ℝ)*Real.log N else 0) +
        (if ¬n.Prime then (C : ℝ)*vonMangoldt n else 0) := by
    have hnN := (mem_Icc.mp hn).2
    by_cases hn1 : n = 1
    · subst n
      simp only [vonMangoldt_apply_one,mul_zero,ite_self,add_zero,Nat.not_prime_one,false_and,if_false]
      split_ifs <;> first | exact mul_nonneg hC hlog | exact le_rfl
    have hn2 : 2 ≤ n := by have := (mem_Icc.mp hn).1; omega
    have hinc : (I n : ℝ) ≤ C := by exact_mod_cast hI (n-1) (by omega) (by omega)
    have hwt := mul_le_mul_of_nonneg_right hinc (vonMangoldt_nonneg (n := n))
    by_cases hp : n.Prime
    · rw [if_neg (not_not.mpr hp),add_zero]
      by_cases hs : n-1 ∈ Nat.smoothNumbers Y
      · have hnG : n ∈ G := mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega,hp⟩,hs⟩
        rw [if_pos hnG,if_neg (by tauto : ¬(n.Prime ∧ n-1 ∉ Nat.smoothNumbers Y)),add_zero]
        exact hwt.trans (mul_le_mul_of_nonneg_left (vonMangoldt_le_log.trans (log_nat_mono hnN)) hC)
      · rw [if_pos (show n.Prime ∧ n-1 ∉ Nat.smoothNumbers Y from ⟨hp,hs⟩)]
        have hwt' : (I n : ℝ)*vonMangoldt n ≤ (I n : ℝ)*Real.log N :=
          mul_le_mul_of_nonneg_left (vonMangoldt_le_log.trans (log_nat_mono hnN)) (Nat.cast_nonneg _)
        split_ifs <;> linarith [mul_nonneg hC hlog]
    · rw [if_pos hp,if_neg (by tauto : ¬(n.Prime ∧ n-1 ∉ Nat.smoothNumbers Y))]
      split_ifs <;> linarith [mul_nonneg hC hlog]
  have hG : (Icc 1 N).filter (fun n => n ∈ G) = G := by
    ext n
    simp only [mem_filter]
    constructor
    · exact fun h => h.2
    · intro hn
      have hp := Nat.mem_primesBelow.mp (mem_filter.mp hn).1
      exact ⟨mem_Icc.mpr ⟨hp.2.pos,by omega⟩,hn⟩
  have hrough : (∑ n ∈ Icc 1 N,
      if n.Prime ∧ n-1 ∉ Nat.smoothNumbers Y then (I n : ℝ)*Real.log N else 0) =
      (∑ d ∈ M, ((roughProgressionPrimes d Y N).card : ℝ))*Real.log N := by
    rw [sum_rough_family_counts_eq_incidence,sum_mul]
    apply sum_congr rfl
    intro n hn
    split_ifs <;> simp only [I,zero_mul]
  calc
    _ = ∑ n ∈ Icc 1 N, (I n : ℝ)*vonMangoldt n := sum_family_progressions_eq_incidence M N
    _ ≤ ∑ n ∈ Icc 1 N,
        ((if n ∈ G then (C : ℝ)*Real.log N else 0) +
        (if n.Prime ∧ n-1 ∉ Nat.smoothNumbers Y then (I n : ℝ)*Real.log N else 0) +
        (if ¬n.Prime then (C : ℝ)*vonMangoldt n else 0)) := sum_le_sum hpoint
    _ = (G.card : ℝ)*((C : ℝ)*Real.log N) +
        (∑ d ∈ M, ((roughProgressionPrimes d Y N).card : ℝ))*Real.log N +
        C*∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime), vonMangoldt n := by
      rw [sum_add_distrib,sum_add_distrib,hrough]
      simp only [← sum_filter,hG,sum_const,nsmul_eq_mul,← mul_sum]
    _ ≤ (G.card : ℝ)*((C : ℝ)*Real.log N) +
        (∑ d ∈ M, ((roughProgressionPrimes d Y N).card : ℝ))*Real.log N +
        C*(2*Real.sqrt N*Real.log N) :=
      _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left (mangoldt_nonprime_sum_le N hN) hC)
    _ = _ := by dsimp only [G]; ring

end Erdos821
