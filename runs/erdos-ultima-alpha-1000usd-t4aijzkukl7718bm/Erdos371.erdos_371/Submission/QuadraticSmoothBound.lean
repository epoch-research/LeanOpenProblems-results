import Submission.PrimeDivisorMoments
import Submission.RoughPartGoodPairs

/-! A quadratic smooth-number upper bound, using squarefree small-prime
logarithmic mass and negligible exceptional rough parts. -/

namespace Erdos371
namespace FiniteSieve
open Finset Filter

lemma log_roughPrimePart_le_squarefreeSmallPrimeLog (R B n : ℕ) (hn : n ≠ 0)
    (hB : Nat.maxPrimeFac n < B)
    (hfree : ∀ p, p.Prime → R < p → ¬p^2 ∣ n) :
    Real.log (roughPrimePart R n) ≤ squarefreeSmallPrimeLog B n := by
  classical
  rw [roughPrimePart, Nat.cast_prod, Real.log_prod]
  · simp only [Nat.cast_pow, Real.log_pow]
    calc
      _ ≤ ∑ p ∈ n.primeFactors with R < p, if p ∣ n then Real.log p else 0 := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hpn,hpR⟩ := mem_filter.mp hp
        have hpp := Nat.prime_of_mem_primeFactors hpn
        have hpd := Nat.dvd_of_mem_primeFactors hpn
        have hv : n.factorization p ≤ 1 := by
          have h := hfree p hpp hpR
          rw [hpp.pow_dvd_iff_le_factorization hn] at h
          omega
        rw [if_pos hpd]
        have hv' : (n.factorization p : ℝ) ≤ 1 := by exact_mod_cast hv
        have hlog := Real.log_nonneg (by exact_mod_cast hpp.one_le : (1 : ℝ) ≤ p)
        nlinarith
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpn,_⟩ := mem_filter.mp hp
          have hpp := Nat.prime_of_mem_primeFactors hpn
          exact Nat.mem_primesBelow.mpr
            ⟨(Nat.le_maxPrimeFac hn hpp (Nat.dvd_of_mem_primeFactors hpn)).trans_lt hB,hpp⟩
        · intro p hp _
          split_ifs
          · exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_le)
          · rfl
  · intro p hp
    exact_mod_cast pow_ne_zero _ (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).ne_zero

lemma squarefreeSmallPrimeLog_large_count_bound (B N : ℕ) (hN : 1 < N) :
    (((range N).filter (fun n => Real.log N ≤ 2*squarefreeSmallPrimeLog B (n+1))).card : ℝ) ≤
      80 * N * (Real.log B / Real.log N)^2 := by
  classical
  let S := (range N).filter (fun n => Real.log N ≤ 2*squarefreeSmallPrimeLog B (n+1))
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hterm (n : ℕ) (hn : n ∈ S) : (Real.log N)^2 ≤ 4*(squarefreeSmallPrimeLog B (n+1))^2 := by
    have hh := (mem_filter.mp hn).2
    have hh' := squarefreeSmallPrimeLog_nonneg B (n+1)
    nlinarith
  have hs : (S.card : ℝ)*(Real.log N)^2 ≤ 80*N*(Real.log B)^2 := by
    calc
      _ = ∑ n ∈ S, (Real.log N)^2 := by simp
      _ ≤ ∑ n ∈ S, 4*(squarefreeSmallPrimeLog B (n+1))^2 := sum_le_sum hterm
      _ ≤ ∑ n ∈ range N, 4*(squarefreeSmallPrimeLog B (n+1))^2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
      _ = 4*∑ n ∈ range N, (squarefreeSmallPrimeLog B (n+1))^2 := (mul_sum _ _ _).symm
      _ ≤ _ := by nlinarith [squarefreeSmallPrimeLog_second_moment B N]
  have hb := (le_div_iff₀ (sq_pos_of_pos hlog)).mpr hs
  convert hb using 1 <;> ring

lemma smooth_count_quadratic_bound (R B N : ℕ) (hN : 1 < N) :
    (((range N).filter (fun n => Nat.maxPrimeFac (n+1) ≤ B)).card : ℝ) ≤
      smallRoughPartCount R N + largePrimeSquareCount R N +
        80 * N * (Real.log (B+1 : ℝ) / Real.log N)^2 := by
  classical
  let T := (range N).filter (fun n => Real.log N ≤ 2*squarefreeSmallPrimeLog (B+1) (n+1))
  have hcover (n : ℕ) (hn : n < N) (hs : Nat.maxPrimeFac (n+1) ≤ B) :
      (roughPrimePart R (n+1))^4 ≤ N^3 ∨
        (∃ p, p.Prime ∧ R<p ∧ p^2 ∣ n+1) ∨ n ∈ T := by
    by_cases h1 : (roughPrimePart R (n+1))^4 ≤ N^3
    · exact Or.inl h1
    by_cases h2 : ∃ p, p.Prime ∧ R<p ∧ p^2 ∣ n+1
    · exact Or.inr (Or.inl h2)
    have hfree : ∀ p, p.Prime → R<p → ¬p^2 ∣ n+1 := by
      intro p hp hpR hd
      exact h2 ⟨p,hp,hpR,hd⟩
    have hlogR : Real.log N ≤ 2*Real.log (roughPrimePart R (n+1)) := by
      have hlt : (N : ℝ)^3 < (roughPrimePart R (n+1) : ℝ)^4 := by exact_mod_cast (lt_of_not_ge h1)
      have hh := Real.log_lt_log (by positivity : (0 : ℝ) < (N : ℝ)^3) hlt
      rw [Real.log_pow,Real.log_pow] at hh
      have hlogN := Real.log_natCast_nonneg N
      norm_num at hh
      linarith
    have hU := log_roughPrimePart_le_squarefreeSmallPrimeLog R (B+1) (n+1) (by omega) (by omega) hfree
    exact Or.inr (Or.inr (mem_filter.mpr ⟨mem_range.mpr hn, by linarith⟩))
  have hc : ((range N).filter (fun n => Nat.maxPrimeFac (n+1) ≤ B)).card ≤
      smallRoughPartCount R N + largePrimeSquareCount R N + T.card := by
    have hsub : (range N).filter (fun n => Nat.maxPrimeFac (n+1) ≤ B) ⊆
        ((range N).filter (fun n => (roughPrimePart R (n+1))^4 ≤ N^3)) ∪
        ((range N).filter (fun n => ∃ p, p.Prime ∧ R<p ∧ p^2 ∣ n+1)) ∪ T := by
      intro n hn
      obtain ⟨hnN,hs⟩ := mem_filter.mp hn
      rcases hcover n (mem_range.mp hnN) hs with h1 | h2 | h3
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hnN,h1⟩))
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hnN,h2⟩))
      · exact mem_union_right _ h3
    exact (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
  have hc' := (Nat.cast_le (α := ℝ)).mpr hc
  simp only [Nat.cast_add] at hc'
  have hT := squarefreeSmallPrimeLog_large_count_bound (B+1) N hN
  push_cast at hT
  exact hc'.trans (add_le_add le_rfl hT)

lemma smooth_count_quadratic_ratio_bound (R B N : ℕ) (hN : 1 < N) :
    (((range N).filter (fun n => Nat.maxPrimeFac (n+1) ≤ B)).card : ℝ) / N ≤
      (smallRoughPartCount R N : ℝ) / N + (largePrimeSquareCount R N : ℝ) / N +
        80 * (Real.log (B+1 : ℝ) / Real.log N)^2 := by
  have hb := div_le_div_of_nonneg_right (smooth_count_quadratic_bound R B N hN)
    (Nat.cast_nonneg (α := ℝ) N)
  have hz : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  convert hb using 1 <;> field_simp

/-- For fixed exponent `u`, the upper density of `N^u`-smooth integers up to
`N` is at most `80*u^2`. The coarse constant suffices when `u` is small. -/
theorem smooth_power_count_eventually_le (u : ℝ) (hu : 0 ≤ u) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (((range N).filter (fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^u)).card : ℝ) / N ≤
        80*u^2+ε := by
  classical
  have hR := smallRoughPartCount_tendsto_zero subpowerCutoff subpowerCutoff_log_ratio_tendsto_zero
  have hS := largePrimeSquareCount_tendsto_zero subpowerCutoff subpowerCutoff_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi := (tendsto_inv_atTop_zero.comp hlog).const_mul (Real.log 2)
  have hu' := (hi.const_add u).pow 2
  have ht := (hR.add hS).add (hu'.const_mul 80)
  simp only [mul_zero, add_zero, zero_add] at ht
  filter_upwards [ht.eventually_lt_const (show 80*u^2 < 80*u^2+ε by linarith),
    eventually_gt_atTop (1 : ℕ)] with N hN hN1
  let B := ⌊(N : ℝ)^u⌋₊
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1.le
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN1)
  have hx1 : (1 : ℝ) ≤ (N : ℝ)^u := Real.one_le_rpow hn1 hu
  have hB : (B : ℝ) ≤ (N : ℝ)^u := Nat.floor_le (Real.rpow_nonneg hn0.le u)
  have hlogB : Real.log (B+1 : ℝ) ≤ Real.log 2 + u*Real.log N := by
    calc
      _ ≤ Real.log (2*(N : ℝ)^u) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hn0 u).ne', Real.log_rpow hn0]
  have hratio : Real.log (B+1 : ℝ)/Real.log N ≤ u+Real.log 2*(Real.log N)⁻¹ := by
    have h := div_le_div_of_nonneg_right hlogB hlogN.le
    convert h using 1 <;> field_simp <;> ring
  have hsq := pow_le_pow_left₀ (div_nonneg (Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) B; linarith)) hlogN.le) hratio 2
  have hcard : ((range N).filter (fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^u)).card ≤
      ((range N).filter (fun n => Nat.maxPrimeFac (n+1) ≤ B)).card := by
    apply card_le_card
    intro n hn
    obtain ⟨hnN,hnp⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hnN,(Nat.le_floor_iff (Real.rpow_nonneg hn0.le u)).mpr hnp⟩
  have hc := div_le_div_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr hcard) (Nat.cast_nonneg (α := ℝ) N)
  have hb := hc.trans (smooth_count_quadratic_ratio_bound (subpowerCutoff N) B N hN1)
  have hsq' := mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 80)
  exact (hb.trans (add_le_add le_rfl hsq')).trans hN.le

#print axioms smooth_count_quadratic_bound
#print axioms smooth_power_count_eventually_le
end FiniteSieve
end Erdos371
