import Submission.PrimeBlockFactorialMoments

/-! Polynomially growing pattern observables are uniformly integrable when
one additional factorial moment is controlled. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

noncomputable def subsetPolynomial (T m : ℕ) : ℝ :=
  ∑ j ∈ range (T+1), (m.choose j : ℝ)

lemma subsetPolynomial_nonneg (T m : ℕ) : 0 ≤ subsetPolynomial T m :=
  sum_nonneg fun _ _ => Nat.cast_nonneg _

lemma subsetPolynomial_mono (T : ℕ) : Monotone (subsetPolynomial T) := by
  intro m n hmn
  exact sum_le_sum fun j _ => by exact_mod_cast Nat.choose_le_choose j hmn

lemma subsetPolynomial_eq_powerset {ι : Type*} (S : Finset ι) (T : ℕ) :
    subsetPolynomial T S.card =
      ∑ E ∈ S.powerset, if E.card ≤ T then (1 : ℝ) else 0 := by
  classical
  rw [sum_powerset]
  have he (j : ℕ) := sum_powersetCard j S (fun k => if k ≤ T then (1 : ℝ) else 0)
  simp_rw [he]
  simp only [nsmul_eq_mul]
  unfold subsetPolynomial
  by_cases h : T ≤ S.card
  · calc
      _ = ∑ j ∈ range (T+1), (S.card.choose j : ℝ)*(if j ≤ T then 1 else 0) := by
        apply sum_congr rfl
        intro j hj
        rw [if_pos (by have := mem_range.mp hj; omega),mul_one]
      _ = _ := by
        apply sum_subset (range_mono (by omega))
        intro j _ hj
        rw [if_neg (by simp only [mem_range] at hj; omega),mul_zero]
  · calc
      _ = ∑ j ∈ range (S.card+1), (S.card.choose j : ℝ) := by
        symm
        apply sum_subset (range_mono (by omega))
        intro j _ hj
        rw [Nat.choose_eq_zero_of_lt (by simp only [mem_range] at hj; omega),Nat.cast_zero]
      _ = _ := by
        apply sum_congr rfl
        intro j hj
        rw [if_pos (by have := mem_range.mp hj; omega),mul_one]

lemma subsetPolynomial_le_factorial_moment (T m : ℕ) (hm : T+1 ≤ m) :
    subsetPolynomial T m ≤ 3^(T+1)*(m.choose (T+1) : ℝ) := by
  rw [← card_range m,subsetPolynomial_eq_powerset]
  calc
    _ ≤ ∑ E ∈ (range m).powerset, if E.card < T+1 then (2 : ℝ)^E.card else 0 := by
      apply sum_le_sum
      intro E _
      by_cases he : E.card ≤ T
      · rw [if_pos he,if_pos (by omega)]
        exact one_le_pow₀ (by norm_num)
      · rw [if_neg he,if_neg (by omega)]
    _ ≤ _ := truncated_powerset_weight_bound (range m) (T+1) (by simpa using hm)

/-- For m above R, one further factorial moment gains a factor tending to
zero as R grows. No probabilistic independence is assumed. -/
lemma subsetPolynomial_high_count_bound (T R m : ℕ) (hR : T+1 < R) (hm : R ≤ m) :
    subsetPolynomial T m  ≤ 
      (3^(T+1)*(T+2 : ℝ)/(R-(T+1) : ℕ))*(m.choose (T+2) : ℝ) := by
  have hRm : 0 < (R-(T+1) : ℕ) := by omega
  have hRr : (0 : ℝ) < (R-(T+1) : ℕ) := by exact_mod_cast hRm
  have hrec : (m.choose (T+2) : ℝ)*(T+2) =
      (m.choose (T+1) : ℝ)*(m-(T+1) : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq m (T+1)
  have hsub : (R-(T+1) : ℕ) ≤ m-(T+1) := Nat.sub_le_sub_right hm _
  have hc : (m.choose (T+1) : ℝ) ≤ 
      (T+2 : ℝ)/(R-(T+1) : ℕ)*(m.choose (T+2) : ℝ) := by
    have he : (T+2 : ℝ)/(R-(T+1) : ℕ)*(m.choose (T+2) : ℝ) =
        ((m.choose (T+2) : ℝ)*(T+2))/(R-(T+1) : ℕ) := by ring
    rw [he]
    apply (le_div_iff₀ hRr).mpr
    rw [hrec]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsub) (Nat.cast_nonneg _)
  calc
    _ ≤ 3^(T+1)*(m.choose (T+1) : ℝ) := subsetPolynomial_le_factorial_moment T m (by omega)
    _ ≤ 3^(T+1)*((T+2 : ℝ)/(R-(T+1) : ℕ)*(m.choose (T+2) : ℝ)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring


/-- A finite averaging version of the high-count estimate. -/
theorem subsetPolynomial_tail_mean_bound {ι : Type*} (X : Finset ι)
    (m : ι → ℕ) (T R : ℕ) (hR : T+1 < R) :
    (∑ x ∈ X, if R ≤ m x then subsetPolynomial T (m x) else 0)/(X.card : ℝ) ≤
      (3^(T+1)*(T+2 : ℝ)/(R-(T+1) : ℕ))*
        ((∑ x ∈ X, (Nat.choose (m x) (T+2) : ℝ))/(X.card : ℝ)) := by
  classical
  rw [← mul_div_assoc, mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro x _
  split_ifs with hm
  · exact subsetPolynomial_high_count_bound T R (m x) hR hm
  · positivity

/-- Uniform integrability of every fixed subset polynomial. The prime
cutoff exponent depends on its degree, not on the tail threshold. -/
theorem prime_pattern_polynomial_tail (T : ℕ) (M ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, T+1 < R ∧ ∀ᶠ N : ℕ in atTop, ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ (N : ℝ)^(1/(4*(T+3 : ℝ)))) →
      (2*∑ p ∈ P, (1 : ℝ)/p) ≤ M →
      (∑ n ∈ range N, if R ≤ (activePrimeAtoms P n).card then
        subsetPolynomial T (activePrimeAtoms P n).card else 0)/(N : ℝ) < ε := by
  let K : ℝ := M^(T+2)/(T+2).factorial+1
  obtain ⟨r,hr⟩ := exists_nat_gt (3^(T+1)*(T+2 : ℝ)*K/ε)
  let R := T+2+r
  have hR : T+1 < R := by dsimp [R]; omega
  have hden : R-(T+1)=r+1 := by dsimp [R]; omega
  have hsmall : (3^(T+1)*(T+2 : ℝ)/(R-(T+1) : ℕ))*K < ε := by
    rw [hden]
    have hpos : (0 : ℝ) < r+1 := by positivity
    rw [show (3^(T+1)*(T+2 : ℝ)/(r+1 : ℕ))*K =
        (3^(T+1)*(T+2 : ℝ)*K)/(r+1) by push_cast; ring]
    apply (div_lt_iff₀ hpos).mpr
    have hh := (div_lt_iff₀ hε).mp hr
    nlinarith
  refine ⟨R,hR,?_⟩
  filter_upwards [prime_pattern_factorial_moment_small_power (T+2) M 1 (by norm_num)] with N hN
  intro P hP hmass
  have hm := hN P (by simpa only [Nat.cast_add,Nat.cast_ofNat,show (2 : ℝ)+1=3 by norm_num,add_assoc] using hP) hmass
  have hb := subsetPolynomial_tail_mean_bound (range N) (fun n => (activePrimeAtoms P n).card) T R hR
  rw [card_range] at hb
  exact (hb.trans (mul_le_mul_of_nonneg_left hm (by positivity))).trans_lt hsmall

#print axioms subsetPolynomial_high_count_bound
end Erdos371.FiniteSieve
