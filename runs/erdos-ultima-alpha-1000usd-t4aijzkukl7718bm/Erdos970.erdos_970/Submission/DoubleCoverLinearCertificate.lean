import Submission.DoubleCoverBandAnalysis

/-! A linear double-cover bound from an explicit selected-pair certificate. -/
namespace Erdos970.DoubleCover
open Finset CoreTailSieve

lemma band_sum_partition (P : Finset ℕ) (f : ℕ → ℝ) (u v w z M : ℕ)
    (huv : u ≤ v) (hvw : v ≤ w) (hwz : w ≤ z) (hzM : z ≤ M) :
    (∑ p ∈ P.filter (fun p => u < p), f p) =
      (∑ p ∈ P.filter (fun p => u < p ∧ p ≤ v), f p) +
      (∑ p ∈ P.filter (fun p => v < p ∧ p ≤ w), f p) +
      (∑ p ∈ P.filter (fun p => w < p ∧ p ≤ z), f p) +
      (∑ p ∈ P.filter (fun p => z < p ∧ p ≤ M), f p) +
      (∑ p ∈ P.filter (fun p => M < p), f p) := by
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  split_ifs <;> simp_all <;> omega

lemma band_sum_split (P : Finset ℕ) (f : ℕ → ℝ) (u v w : ℕ)
    (huv : u ≤ v) (hvw : v ≤ w) :
    (∑ p ∈ P.filter (fun p => u < p ∧ p ≤ w), f p) =
      (∑ p ∈ P.filter (fun p => u < p ∧ p ≤ v), f p) +
      (∑ p ∈ P.filter (fun p => v < p ∧ p ≤ w), f p) := by
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  split_ifs <;> simp_all <;> omega

/-- A small exact core and a sparse selected-pair certificate imply a linear
length bound. The no-triple-hit condition remains explicit. -/
theorem linear_of_selected_certificate (Q R : Finset ℕ) (F : Finset (Finset ℕ))
    (hQ : ∀ q ∈ Q, q.Prime) (hR : ∀ p ∈ R, p.Prime)
    (hdis : Disjoint Q R) (hF : F ⊆ R.powersetCard 2) (r : ℕ → ℕ) (m k : ℕ)
    (hm : 0 < m) (hk : 0 < k) (hQcard : Q.card ≤ 2) (hRcard : R.card ≤ k)
    (hcover : ∀ x < m, ∃ p ∈ Q ∪ R, x ≡ r p [MOD p])
    (hdouble : ∀ x < m, (R.filter (fun p => x ≡ r p [MOD p])).card ≤ 2)
    (hFcard : (F.card : ℝ) ≤ (m : ℝ) / 5000)
    (hmargin : 1 / 100 - (k : ℝ) / m ≤
      1 - (∑ p ∈ R, 1 / (p : ℝ)) + ∑ T ∈ F, 1 / ∏ p ∈ T, (p : ℝ)) :
    m ≤ 6000 * k := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hRcardR : (R.card : ℝ) ≤ k := by exact_mod_cast hRcard
  have hQcardR : (Q.card : ℝ) ≤ 2 := by exact_mod_cast hQcard
  have hden := (BrunCriterion.prime_product_bounds Q hQ).1
  change 1 / ((Q.card : ℝ) + 1) ≤ density Q at hden
  have hden4 : (1 : ℝ) / 4 ≤ density Q := by
    have h := (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < Q.card + 1)
      (by linarith : (Q.card : ℝ) + 1 ≤ 4)).trans hden
    exact h
  have hden0 : 0 ≤ density Q := by linarith
  have hden1 : density Q ≤ 1 := by
    apply prod_le_one
    · intro p hp
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (hQ p hp).two_le
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpR
      linarith
    · intro p hp
      have : 0 ≤ 1 / (p : ℝ) := by positivity
      linarith
  have hlow : (m : ℝ) / 400 - k ≤ (m : ℝ) * density Q *
      (1 - (∑ p ∈ R, 1 / (p : ℝ)) + ∑ T ∈ F, 1 / ∏ p ∈ T, (p : ℝ)) := by
    have hd := mul_le_mul_of_nonneg_left hden4 hmR.le
    have hd' := mul_le_mul_of_nonneg_left hden1 (Nat.cast_nonneg k)
    calc
      _ ≤ (m : ℝ) * density Q / 100 - k * density Q := by nlinarith only [hd, hd']
      _ = (m : ℝ) * density Q * (1 / 100 - (k : ℝ) / m) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hmargin (mul_nonneg hmR.le hden0)
  have hc := cover_selected_pairs_bound Q R F hQ hR hdis hF r m hcover hdouble
  have hpow : (2 : ℝ) ^ Q.card ≤ 4 := by
    convert pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hQcard using 1
    norm_num
  have hcost : (2 : ℝ) ^ Q.card * (1 + R.card + F.card) ≤
      4 * (1 + (k : ℝ) + (m : ℝ) / 5000) := by
    apply mul_le_mul hpow (by linarith) (by positivity) (by norm_num)
  have hlast : (m : ℝ) ≤ 6000 * k := by linarith [hlow.trans (hc.trans hcost)]
  exact_mod_cast hlast

#print axioms linear_of_selected_certificate
end Erdos970.DoubleCover
