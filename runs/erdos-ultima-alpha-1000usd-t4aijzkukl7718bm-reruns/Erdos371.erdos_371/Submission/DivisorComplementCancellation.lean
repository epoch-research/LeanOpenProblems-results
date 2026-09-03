import FormalConjecturesUtil

/-! Exact signed cancellation for ALL pairs of divisors of consecutive
positive integers. The prime-divisor restriction is not preserved by the
involution, so this does not establish Erdős 371. -/

namespace Erdos371DivisorComplementCancellation

open Finset

def compare (d e : ℕ) : ℤ := if d<e then 1 else -1

/-- For two factorizations of successive positive integers, increasing one
factor is equivalent to not increasing the complementary factor. -/
lemma complementary_order {a b d e n : ℕ} (ha : 0<a) (hd : 0<d)
    (han : a*d=n) (hbn : b*e=n+1) : d<e ↔ ¬a<b := by
  constructor
  · intro hde hab
    have hh := Nat.mul_le_mul (show a+1≤b by omega) (show d+1≤e by omega)
    nlinarith
  · intro hab
    by_contra hde
    have hh := Nat.mul_le_mul (show b≤a by omega) (show e≤d by omega)
    omega

lemma complementary_sign {a b d e n : ℕ} (ha : 0<a) (hd : 0<d)
    (han : a*d=n) (hbn : b*e=n+1) : compare d e = -compare a b := by
  have hh := complementary_order ha hd han hbn
  unfold compare
  by_cases h : a<b <;> simp [h,hh]

lemma divisor_complementary_sign {n d e : ℕ} (hn : 0<n)
    (hd : d ∈ n.divisors) (he : e ∈ (n+1).divisors) :
    compare d e = -compare (n/d) ((n+1)/e) := by
  have hdn := (Nat.mem_divisors.mp hd).1
  have hen := (Nat.mem_divisors.mp he).1
  have hd0 : 0<d := Nat.pos_of_dvd_of_pos hdn hn
  have ha : 0<n/d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  exact complementary_sign ha hd0 (Nat.div_mul_cancel hdn) (Nat.div_mul_cancel hen)

/-- Complementation is a sign-reversing permutation of the full divisor
product. This identity includes the divisor one and the full divisors. -/
theorem all_divisor_comparison_sum {n : ℕ} (hn : 0<n) :
    (∑ d ∈ n.divisors, ∑ e ∈ (n+1).divisors, compare d e) = 0 := by
  have hc : (∑ d ∈ n.divisors, ∑ e ∈ (n+1).divisors,
      compare (n/d) ((n+1)/e)) =
      ∑ d ∈ n.divisors, ∑ e ∈ (n+1).divisors, compare d e := by
    simp_rw [Nat.sum_div_divisors]
    exact Nat.sum_div_divisors n (fun d => ∑ e ∈ (n+1).divisors, compare d e)
  have hh : (∑ d ∈ n.divisors, ∑ e ∈ (n+1).divisors, compare d e) =
      -(∑ d ∈ n.divisors, ∑ e ∈ (n+1).divisors, compare d e) := by
    calc
      _ = ∑ d ∈ n.divisors, ∑ e ∈ (n+1).divisors, -compare (n/d) ((n+1)/e) := by
        apply sum_congr rfl
        intro d hd
        apply sum_congr rfl
        intro e he
        exact divisor_complementary_sign hn hd he
      _ = _ := by simp_rw [sum_neg_distrib]; rw [hc]
  omega

/-- Precisely half the full divisor pairs have their first divisor smaller.
This is a statement about divisor pairs, not about the largest pair. -/
theorem all_divisor_ascent_count {n : ℕ} (hn : 0<n) :
    2*(((n.divisors.product (n+1).divisors).filter (fun de => de.1<de.2)).card) =
      n.divisors.card*(n+1).divisors.card := by
  have hs := all_divisor_comparison_sum hn
  have he (d e : ℕ) : compare d e = 2*(if d<e then (1:ℤ) else 0)-1 := by
    unfold compare
    split_ifs <;> norm_num
  simp_rw [he] at hs
  rw [← sum_product n.divisors (n+1).divisors
    (fun de : ℕ×ℕ => 2*(if de.1<de.2 then (1:ℤ) else 0)-1)] at hs
  simp only [sum_sub_distrib,← mul_sum,sum_boole,sum_const,nsmul_eq_mul,mul_one,
    card_product] at hs
  have hz := sub_eq_zero.mp hs
  have hh : (2:ℤ)*(((n.divisors.product (n+1).divisors).filter
      (fun de => de.1<de.2)).card:ℤ) = (n.divisors.card:ℤ)*(n+1).divisors.card := by
    convert hz using 1
  exact_mod_cast hh

end Erdos371DivisorComplementCancellation

#print axioms Erdos371DivisorComplementCancellation.all_divisor_comparison_sum
#print axioms Erdos371DivisorComplementCancellation.all_divisor_ascent_count
