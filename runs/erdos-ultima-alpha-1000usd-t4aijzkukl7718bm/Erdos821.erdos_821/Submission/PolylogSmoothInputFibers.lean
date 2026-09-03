import Submission.UniformClosedFibers

/-!
# Large squarefree fibers with polylogarithmically bounded input primes

The existing smooth-predecessor count supplies these stronger input-size
properties without changing the multiplicity exponent. No distribution
of primes in progressions to these input moduli is asserted here, and the
near-linear conjecture remains unresolved.
-/

open Nat Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma dyadic_card_le_four_log_output (k n : ℕ) (hk : 2 ≤ k)
    (hn : 2^(k-1) ≤ n) : (k : ℝ) ≤ 4*Real.log (n : ℝ) := by
  have hp : (0 : ℝ) < (2 : ℝ)^(k-1) := by positivity
  have hlog := Real.log_le_log hp (show (2 : ℝ)^(k-1) ≤ n by exact_mod_cast hn)
  rw [Real.log_pow, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one] at hlog
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hhalf : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [mul_le_mul_of_nonneg_left hhalf (show 0 ≤ (k : ℝ)-1 by linarith)]

lemma polylog_input_fibers_of_general_density (t a b : ℕ)
    (hbt : b+4 ≤ t) (hba : b+3 ≤ a) (hat : a ≤ t)
    (H : ∀ M : ℕ, ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2^(t*L) ∧
        p-1 ∈ Nat.smoothNumbers (2^(b*L))) ∧ 2^(a*L) ≤ P.card)
    (N : ℕ) :
    ∃ (n : ℕ) (F : Finset ℕ), N<n ∧
      (n : ℝ)^((a-b-2 : ℕ)/(t : ℝ)) < F.card ∧
      ∀ m ∈ F, Squarefree m ∧ totient m=n ∧
        ∀ p ∈ m.primeFactors,
          (p : ℝ) ≤ (4*Real.log (n : ℝ))^((t : ℝ)/(b+1)) := by
  have htR : (0 : ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have hδ : 0 < ((a-b-2 : ℕ) : ℝ)/(t : ℝ) := by
    apply div_pos _ htR
    exact_mod_cast (show 0<a-b-2 by omega)
  obtain ⟨L,hLM,P,hP,hcard⟩ := H (max 1 (max t N))
  have hL : 1 ≤ L := (le_max_left _ _).trans hLM
  have htL : t ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLM)
  have hNL : N ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hLM)
  let k := 2^((b+1)*L)
  let y := 2^(b*L)
  have hk : 2 ≤ k := by
    have he : 1 ≤ (b+1)*L := Nat.mul_pos (by omega) hL
    exact (by norm_num : 2 = 2^1).le.trans (Nat.pow_le_pow_right (by decide) he)
  have hLk : L ≤ k-1 := by
    have hLp := Nat.lt_two_pow_self (n := L)
    have hmul : 2^L ≤ k := Nat.pow_le_pow_right (by decide)
      (Nat.le_mul_of_pos_left _ (by omega))
    omega
  have hmargin : ((t*L*k+1)^y : ℝ)*(2 : ℝ)^((a-b-2)*L*k) <
      (P.card.choose k : ℝ) := by
    exact_mod_cast (general_smooth_prime_counting_margin t a b L hbt hba hat hL htL).trans_le
      (Nat.choose_le_choose k hcard)
  obtain ⟨n,F,hnlo,hnhi,hFcard,hF⟩ := large_squarefree_fiber_of_smooth_shifted_primes
    P (t*L) y k ((2 : ℝ)^((a-b-2)*L*k)) (by positivity) hP
    (by simpa only [Nat.cast_mul] using hmargin)
  have hNn : N<n := hNL.trans_lt ((Nat.lt_two_pow_self (n := L)).trans_le
    ((Nat.pow_le_pow_right (by decide) hLk).trans hnlo))
  have hexp : ((t*L*k : ℕ) : ℝ)*(((a-b-2 : ℕ) : ℝ)/t) =
      (((a-b-2)*L*k : ℕ) : ℝ) := by
    push_cast
    field_simp
  have hpow : (n : ℝ)^((a-b-2 : ℕ)/(t : ℝ)) ≤ (2 : ℝ)^((a-b-2)*L*k) := by
    calc
      _ ≤ ((2 : ℝ)^(t*L*k))^((a-b-2 : ℕ)/(t : ℝ)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hnhi) hδ.le
      _ = (2 : ℝ)^(((t*L*k : ℕ) : ℝ)*(((a-b-2 : ℕ) : ℝ)/t)) :=
        (Real.rpow_natCast_mul (by norm_num) _ _).symm
      _ = _ := by rw [hexp,Real.rpow_natCast]
  refine ⟨n,F,hNn,hpow.trans_lt hFcard,?_⟩
  intro m hm
  refine ⟨(hF m hm).1,(hF m hm).2.1,?_⟩
  intro p hp
  have hpB : (p : ℝ) ≤ (2 : ℝ)^(t*L) := by
    exact_mod_cast (hP p ((hF m hm).2.2.2 hp)).2.1
  have heq : (2 : ℝ)^(t*L) = (k : ℝ)^((t : ℝ)/(b+1)) := by
    dsimp [k]
    rw [Nat.cast_pow,Nat.cast_ofNat,← Real.rpow_natCast_mul (by norm_num),
      ← Real.rpow_natCast]
    congr 1
    push_cast
    field_simp
  exact (hpB.trans_eq heq).trans
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (dyadic_card_le_four_log_output k n hk hnlo)
      (by positivity))

lemma polylog_input_fibers_of_eventual_polynomial_count (t b K C d : ℕ)
    (hb : 0<b) (hbt : b<t)
    (H : ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2^(t*m) ∧
        p-1 ∈ Nat.smoothNumbers (K*2^(b*m))) ∧
      2^(t*m) ≤ C*(m+1)^d*P.card)
    (γ : ℝ) (hγ : γ<1-(b : ℝ)/t) (N : ℕ) :
    ∃ (n : ℕ) (F : Finset ℕ), N<n ∧ (n : ℝ)^γ < F.card ∧
      ∀ m ∈ F, Squarefree m ∧ totient m=n ∧
        ∀ p ∈ m.primeFactors,
          (p : ℝ) ≤ (4*Real.log (n : ℝ))^((t : ℝ)/b) := by
  have ht : 0<t := hb.trans hbt
  have htR : (0 : ℝ)<t := by exact_mod_cast ht
  have hbR : (0 : ℝ)<b := by exact_mod_cast hb
  have hγ' : γ < ((t : ℝ)-b)/t := by
    convert hγ using 1
    field_simp
  have hmargin : 0 < (t : ℝ)-b-t*γ := by
    have h := (lt_div_iff₀ htR).mp hγ'
    nlinarith only [h]
  obtain ⟨k,hk⟩ := exists_nat_gt (max 5 (4/((t : ℝ)-b-t*γ)))
  have hk5R : (5 : ℝ)<k := (le_max_left _ _).trans_lt hk
  have hk5 : 5 ≤ k := by exact_mod_cast hk5R.le
  have h4 : 4 < (k : ℝ)*((t : ℝ)-b-t*γ) :=
    (div_lt_iff₀ hmargin).mp ((le_max_right _ _).trans_lt hk)
  have hgap : b*k+5 ≤ t*k := by
    have h := Nat.mul_le_mul_right k (show b+1 ≤ t by omega)
    nlinarith only [h,hk5]
  have hnum : ((t*k-1-(b*k+1)-2 : ℕ) : ℝ) = (t : ℝ)*k-b*k-4 := by
    rw [Nat.cast_sub (by omega : 2 ≤ t*k-1-(b*k+1)),
      Nat.cast_sub (by omega : b*k+1 ≤ t*k-1),Nat.cast_sub (by omega : 1 ≤ t*k)]
    push_cast
    ring
  have htkR : (0 : ℝ)<(t*k : ℕ) := by
    exact_mod_cast Nat.mul_pos ht (by omega : 0<k)
  have hγk : γ < ((t*k-1-(b*k+1)-2 : ℕ) : ℝ)/(t*k : ℕ) := by
    apply (lt_div_iff₀ htkR).mpr
    rw [hnum,Nat.cast_mul]
    nlinarith only [h4]
  obtain ⟨n,F,hn,hcard,hF⟩ := polylog_input_fibers_of_general_density
    (t*k) (t*k-1) (b*k+1) (by omega) (by omega) (by omega)
    (dyadic_family_of_eventual_polynomial_count t b K C d k ht (by omega) H) (max N 1)
  have hn1 : 1<n := (le_max_right _ _).trans_lt hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1.le
  have hbase : 1 ≤ 4*Real.log (n : ℝ) := by
    have hlog : Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn1)
    linarith [Real.log_two_gt_d9]
  have hratio : ((t*k : ℕ) : ℝ)/((b*k+1 : ℕ)+1) ≤ (t : ℝ)/b := by
    push_cast
    apply (div_le_div_iff₀ (by positivity) hbR).mpr
    nlinarith only [htR.le]
  refine ⟨n,F,(le_max_left _ _).trans_lt hn,
    (Real.rpow_le_rpow_of_exponent_le hnR hγk.le).trans_lt hcard,?_⟩
  intro m hm
  refine ⟨(hF m hm).1,(hF m hm).2.1,?_⟩
  intro p hp
  exact ((hF m hm).2.2 p hp).trans
    (Real.rpow_le_rpow_of_exponent_le hbase hratio)

/-- Every presently supplied multiplicity exponent is attained by squarefree
inputs with all prime factors bounded by a fixed power of log n. -/
theorem wide_block_polylog_input_fibers (γ : ℝ)
    (hγ : γ<1036568/2000001) (N : ℕ) :
    ∃ (n : ℕ) (F : Finset ℕ), N<n ∧ (n : ℝ)^γ < F.card ∧
      ∀ m ∈ F, Squarefree m ∧ totient m=n ∧
        ∀ p ∈ m.primeFactors,
          (p : ℝ) ≤ (4*Real.log (n : ℝ))^(2000001/963433 : ℝ) := by
  obtain ⟨C,_hC,H⟩ := exists_wide_block_smooth_prime_count
  rw [show (2000001/963433 : ℝ) =
    ((64*40000020 : ℕ) : ℝ)/((64*19268660 : ℕ) : ℝ) by norm_num]
  apply polylog_input_fibers_of_eventual_polynomial_count (64*40000020) (64*19268660)
    1 C 1 (by omega) (by omega) ?_ γ ?_ N
  · filter_upwards [H] with m hm
    refine ⟨smoothPrimePool (independentN 40000020 m) (independentN 19268660 m),?_,?_⟩
    · intro p hp
      obtain ⟨hp,hs⟩ := Finset.mem_filter.mp hp
      obtain ⟨hN,hpr⟩ := Nat.mem_primesBelow.mp hp
      refine ⟨hpr,?_,?_⟩
      · change p ≤ independentN 40000020 m
        omega
      · simpa only [one_mul] using hs
    · have hh : independentN 40000020 m ≤
          C*m*(smoothPrimePool (independentN 40000020 m) (independentN 19268660 m)).card := by
        exact_mod_cast hm
      exact hh.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C (by simp)))
  · norm_num
    exact hγ

end Erdos821
