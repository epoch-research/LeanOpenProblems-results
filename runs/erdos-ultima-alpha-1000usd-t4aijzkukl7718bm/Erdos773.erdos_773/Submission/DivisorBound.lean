import FormalConjecturesUtil

/-! A uniform subpower bound for the divisor function. -/

namespace Erdos773

open Finset Filter

lemma divisor_card_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ := by
  let b : ℝ := 2 ^ δ
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) hδ
  let c : ℝ := 1 + 1 / (b - 1)
  have hc : 1 ≤ c := by
    dsimp [c]
    have : 0 ≤ 1 / (b - 1) := div_nonneg zero_le_one (by linarith)
    linarith
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hcb : c * (b - 1) = b := by
    dsimp [c]
    field_simp [show b - 1 ≠ 0 by linarith]
    <;> ring
  have hsmall (e : ℕ) : (e : ℝ) + 1 ≤ c * b ^ e := by
    have hber := one_add_mul_sub_le_pow (by linarith : -1 ≤ b) e
    calc
      (e : ℝ) + 1 ≤ c + (e : ℝ) * b := by
        nlinarith [mul_nonneg (Nat.cast_nonneg e) (le_of_lt (sub_pos.mpr hb))]
      _ = c * (1 + (e : ℝ) * (b - 1)) := by
        rw [mul_add, mul_one, ← mul_left_comm, hcb]
      _ ≤ c * b ^ e := mul_le_mul_of_nonneg_left hber hcpos.le
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ p ≥ K, (2 : ℝ) ≤ (p : ℝ) ^ δ := by
    exact eventually_atTop.mp
      (tendsto_atTop.mp ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop) 2)
  refine ⟨c ^ K, pow_pos hcpos _, ?_⟩
  intro n
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow hδ.ne']
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p + 1 : ℕ) ≤
        (if p < K then c else 1) * ((p : ℝ) ^ δ) ^ n.factorization p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hpk : p < K
    · rw [if_pos hpk]
      calc
        ((n.factorization p + 1 : ℕ) : ℝ) = (n.factorization p : ℝ) + 1 := by push_cast; rfl
        _ ≤ c * b ^ n.factorization p := hsmall _
        _ ≤ c * ((p : ℝ) ^ δ) ^ n.factorization p := by
          apply mul_le_mul_of_nonneg_left _ hcpos.le
          apply pow_le_pow_left₀ (by positivity)
          exact Real.rpow_le_rpow (by norm_num) hp2 hδ.le
    · rw [if_neg hpk, one_mul]
      calc
        ((n.factorization p + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n.factorization p := by
          exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n.factorization p)))
        _ ≤ ((p : ℝ) ^ δ) ^ n.factorization p :=
          pow_le_pow_left₀ (by norm_num) (hK p (by omega)) _
  have hcoeff : (∏ p ∈ n.primeFactors, if p < K then c else 1) ≤ c ^ K := by
    have hcard : (n.primeFactors.filter (· < K)).card ≤ K := by
      calc
        _ ≤ (Finset.range K).card := Finset.card_le_card (by
          intro p hp
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
        _ = K := Finset.card_range K
    simpa [Finset.prod_ite] using pow_le_pow_right₀ hc hcard
  have hnprod : (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = n := by
    have hnprod' : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
      rw [← Nat.prod_factorization_eq_prod_primeFactors, Nat.factorization_prod_pow_eq_self hn]
    exact_mod_cast hnprod'
  have hrpow : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ n.factorization p) = (n : ℝ) ^ δ := by
    calc
      _ = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ δ := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p),
          ← Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_comm δ]
      _ = (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) ^ δ :=
        Real.finset_prod_rpow _ _ (by intros; positivity) _
      _ = (n : ℝ) ^ δ := by rw [hnprod]
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) := by
      rw [Nat.card_divisors hn, Nat.cast_prod]
    _ ≤ ∏ p ∈ n.primeFactors, (if p < K then c else 1) * ((p : ℝ) ^ δ) ^ n.factorization p :=
      Finset.prod_le_prod (by intros; positivity) hfactor
    _ = (∏ p ∈ n.primeFactors, if p < K then c else 1) * (n : ℝ) ^ δ := by
      rw [Finset.prod_mul_distrib, hrpow]
    _ ≤ c ^ K * (n : ℝ) ^ δ := mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (Nat.cast_nonneg n) δ)

#print axioms divisor_card_subpower

end Erdos773
