import Submission.ComparableSlopeMean
import Submission.ReciprocalDiscrepancy

/-! Applying the finite two-linear-form sieve to adjacent integers with
prescribed prime cofactors. -/

namespace Erdos371
namespace FiniteSieve
open Finset

def cofactorPrimePairSet (N a b z : ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun n => a ∣ n ∧ b ∣ n+1 ∧
    (n/a).Prime ∧ ((n+1)/b).Prime ∧ z < n/a ∧ z < (n+1)/b

lemma adjacentRoot_residue (a b n : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (han : a ∣ n) (hbn : b ∣ n+1) :
    n % (a*b) = adjacentRoot a b hab := by
  have h1 : Nat.ModEq a n (adjacentRoot a b hab) :=
    han.modEq_zero_nat.trans (adjacentRoot_dvd_left a b hab).zero_modEq_nat
  have h2 : Nat.ModEq b n (adjacentRoot a b hab) :=
    (hbn.modEq_zero_nat.trans (adjacentRoot_dvd_right a b hab hb).zero_modEq_nat).add_right_cancel' 1
  have h := (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨h1,h2⟩
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt (adjacentRoot_lt a b hab ha hb)] using h

lemma prime_quotient_linear_forms (a b n : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (han : a ∣ n) (hbn : b ∣ n+1) :
    n/a = b*(n/(a*b)) + adjacentRoot a b hab/a ∧
      (n+1)/b = a*(n/(a*b)) + (adjacentRoot a b hab+1)/b := by
  have hmod := adjacentRoot_residue a b n ha hb hab han hbn
  have hdecomp := Nat.mod_add_div n (a*b)
  rw [hmod] at hdecomp
  have hleft := Nat.mul_div_cancel' (adjacentRoot_dvd_left a b hab)
  have hright := Nat.mul_div_cancel' (adjacentRoot_dvd_right a b hab hb)
  have hn := Nat.mul_div_cancel' han
  have hn' := Nat.mul_div_cancel' hbn
  constructor
  · apply Nat.eq_of_mul_eq_mul_left ha
    nlinarith
  · apply Nat.eq_of_mul_eq_mul_left hb
    nlinarith

lemma cofactorPrimePairSet_empty_of_not_coprime (N a b z : ℕ) (hab : ¬a.Coprime b) :
    cofactorPrimePairSet N a b z = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨_, han, hbn, _⟩ := mem_filter.mp hn
  exact hab (Nat.Coprime.of_dvd han hbn (by simp))

lemma cofactorPrimePairSet_card_le_linear (N a b z : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) :
    (cofactorPrimePairSet N a b z).card ≤
      ((range (N/(a*b)+1)).filter fun t =>
        (b*t+adjacentRoot a b hab/a).Prime ∧
        (a*t+(adjacentRoot a b hab+1)/b).Prime ∧
        z < b*t+adjacentRoot a b hab/a ∧ z < a*t+(adjacentRoot a b hab+1)/b).card := by
  apply card_le_card_of_injOn (fun n => n/(a*b))
  · intro n hn
    simp only [mem_coe] at hn ⊢
    obtain ⟨hn, han, hbn, hp, hq, hzp, hzq⟩ := mem_filter.mp hn
    have he := prime_quotient_linear_forms a b n ha hb hab han hbn
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_Icc.mp hn).2)), ?_⟩
    simpa only [← he.1, ← he.2] using ⟨hp,hq,hzp,hzq⟩
  · intro n hn m hm hnm
    simp only [mem_coe] at hn hm
    obtain ⟨_, han, hbn, _⟩ := mem_filter.mp hn
    obtain ⟨_, ham, hbm, _⟩ := mem_filter.mp hm
    have hnmod := adjacentRoot_residue a b n ha hb hab han hbn
    have hmmod := adjacentRoot_residue a b m ha hb hab ham hbm
    have hn' := Nat.mod_add_div n (a*b)
    have hm' := Nat.mod_add_div m (a*b)
    change n/(a*b) = m/(a*b) at hnm
    rw [hnmod, hnm] at hn'
    rw [hmmod] at hm'
    omega

lemma cofactorPrimePairSet_bound (N a b z : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hz : 1 ≤ z) :
    ((cofactorPrimePairSet N a b z).card : ℝ) ≤
      2*Real.exp 2 * slopeSieveFactor (a*b) * ((N/(a*b)+1 : ℕ) : ℝ) /
        (Real.log (z+1 : ℝ))^2 +
      (2*brunDegree z+1 : ℕ) * (z : ℝ)^(4*brunDegree z) := by
  by_cases hab : a.Coprime b
  · have hdet : (adjacentRoot a b hab/a)*a+1 = b*((adjacentRoot a b hab+1)/b) := by
      rw [Nat.div_mul_cancel (adjacentRoot_dvd_left a b hab),
        Nat.mul_div_cancel' (adjacentRoot_dvd_right a b hab hb)]
    have h := twoLinear_prime_count_log_bound b (adjacentRoot a b hab/a)
      a ((adjacentRoot a b hab+1)/b) (N/(a*b)+1) z hb ha hz (Or.inr hdet)
    have hc := cofactorPrimePairSet_card_le_linear N a b z ha hb hab
    have hcR := (Nat.cast_le (α := ℝ)).mpr hc
    exact hcR.trans (by simpa only [Nat.mul_comm b a] using h)
  · rw [cofactorPrimePairSet_empty_of_not_coprime N a b z hab, card_empty, Nat.cast_zero]
    unfold slopeSieveFactor
    positivity

/-- If the cofactor product does not exceed the endpoint, the length of the
linear-form parameter interval is at most twice `N/(a*b)`. -/
theorem cofactorPrimePairSet_bound_of_product_le (N a b z : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 ≤ z) (habN : a*b ≤ N) :
    ((cofactorPrimePairSet N a b z).card : ℝ) ≤
      (4*Real.exp 2*N/(Real.log (z+1 : ℝ))^2) * (slopeSieveFactor (a*b)/((a : ℝ)*b)) +
      (2*brunDegree z+1 : ℕ) * (z : ℝ)^(4*brunDegree z) := by
  have hab0 : (0 : ℝ) < (a : ℝ)*b := by exact_mod_cast Nat.mul_pos ha hb
  have hN : (a : ℝ)*b ≤ N := by exact_mod_cast habN
  have hdiv : ((N/(a*b)+1 : ℕ) : ℝ) ≤ 2*(N : ℝ)/((a : ℝ)*b) := by
    have hfloor := Nat.cast_div_le (m := N) (n := a*b) (α := ℝ)
    have hone : (1 : ℝ) ≤ N/((a : ℝ)*b) := (le_div_iff₀ hab0).mpr (by simpa using hN)
    push_cast at hfloor ⊢
    convert add_le_add hfloor hone using 1; ring
  refine (cofactorPrimePairSet_bound N a b z ha hb hz).trans (add_le_add ?_ le_rfl)
  have ht := mul_le_mul_of_nonneg_left hdiv
    (show 0 ≤ 2*Real.exp 2*slopeSieveFactor (a*b)/(Real.log (z+1 : ℝ))^2 by
      unfold slopeSieveFactor; positivity)
  convert ht using 1 <;> ring

#print axioms cofactorPrimePairSet_bound_of_product_le
end FiniteSieve
end Erdos371
