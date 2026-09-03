import FormalConjecturesUtil

/-! A counting obstruction to replacing prime products by products of arbitrary
indices. This file makes no claim about the Jacobsthal conjecture. -/
namespace Erdos970.IndexSupportCost
open Finset

/-- Subsets of integer indices whose product is at most the cutoff. -/
def indexSupport (R : ℕ) : Finset (Finset ℕ) :=
  (Icc 2 R).powerset.filter (fun T => ∏ i ∈ T, i ≤ R)

lemma mem_indexSupport (R : ℕ) (T : Finset ℕ) :
    T ∈ indexSupport R ↔ T ⊆ Icc 2 R ∧ ∏ i ∈ T, i ≤ R := by
  simp [indexSupport]

/-- The two-element subsets alone give a harmonic lower bound. -/
theorem pair_count_le (N R : ℕ) (hNR : N ≤ R) :
    (∑ a ∈ Icc 2 N, (R / a + 1 - (N + 1))) ≤ (indexSupport R).card := by
  let S := (Icc 2 N).sigma (fun a => Icc (N+1) (R/a))
  have hc := card_le_card_of_injOn (s := S) (t := indexSupport R)
    (f := fun x : Σ _ : ℕ, ℕ => ({x.1, x.2} : Finset ℕ))
  have hmap : ∀ x ∈ S, ({x.1, x.2} : Finset ℕ) ∈ indexSupport R := by
    intro x hx
    obtain ⟨ha, hb⟩ := mem_sigma.mp hx
    obtain ⟨ha2, haN⟩ := mem_Icc.mp ha
    obtain ⟨hbN, hbR⟩ := mem_Icc.mp hb
    have hab : x.1 ≠ x.2 := by omega
    rw [mem_indexSupport]
    constructor
    · intro c hc
      simp only [mem_insert, mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact mem_Icc.mpr ⟨ha2, haN.trans hNR⟩
      · exact mem_Icc.mpr ⟨by omega, hbR.trans (Nat.div_le_self _ _)⟩
    · rw [prod_pair hab]
      simpa [Nat.mul_comm] using Nat.mul_le_of_le_div x.1 x.2 R hbR
  have hinj : Set.InjOn (fun x : Σ _ : ℕ, ℕ => ({x.1, x.2} : Finset ℕ)) ↑S := by
    intro x hx y hy he
    dsimp only at he
    obtain ⟨ha, hb⟩ := mem_sigma.mp hx
    obtain ⟨hc, hd⟩ := mem_sigma.mp hy
    have ha' := mem_Icc.mp ha
    have hb' := mem_Icc.mp hb
    have hc' := mem_Icc.mp hc
    have hd' := mem_Icc.mp hd
    have hxy1 : x.1 = y.1 := by
      have hm : x.1 ∈ ({y.1, y.2} : Finset ℕ) := by rw [← he]; simp
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with h | h
      · exact h
      · omega
    have hxy2 : x.2 = y.2 := by
      have hm : x.2 ∈ ({y.1, y.2} : Finset ℕ) := by rw [← he]; simp
      simp only [mem_insert, mem_singleton] at hm
      rcases hm with h | h
      · omega
      · exact h
    exact Sigma.ext hxy1 (heq_of_eq hxy2)
  simpa only [S, card_sigma, Nat.card_Icc] using hc hmap hinj

lemma fiber_cast_lower (N R a : ℕ) (ha : 0 < a) (hd : a ∣ R) :
    (R : ℝ) / a - N ≤ ((R / a + 1 - (N + 1) : ℕ) : ℝ) := by
  have he : ((R/a : ℕ) : ℝ) = (R : ℝ) / a :=
    Nat.cast_div hd (by exact_mod_cast ha.ne')
  rw [← he]
  have h : R/a ≤ (R/a + 1 - (N+1)) + N := by omega
  have h' : ((R/a : ℕ) : ℝ) ≤ ((R/a + 1 - (N+1) : ℕ) : ℝ) + N := by exact_mod_cast h
  linarith

/-- At cutoffs divisible by every small index, the support-to-cutoff ratio
is bounded below by a harmonic sum, up to a boundary term. -/
theorem harmonic_lower (N R : ℕ) (hN : 2 ≤ N) (hNR : N ≤ R)
    (hd : ∀ a ∈ Icc 2 N, a ∣ R) :
    (R : ℝ) * ((harmonic N : ℝ) - 1) - N * (N - 1 : ℝ) ≤
      ((indexSupport R).card : ℝ) := by
  have hsum : (∑ a ∈ Icc 2 N, (a : ℝ)⁻¹) = (harmonic N : ℝ) - 1 := by
    have he : Icc 1 N = insert 1 (Icc 2 N) := by
      ext a
      simp only [mem_Icc, mem_insert]
      omega
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, he]
    rw [sum_insert (by simp)]
    norm_num
  calc
    _ = ∑ a ∈ Icc 2 N, ((R : ℝ) / a - N) := by
      simp_rw [div_eq_mul_inv]
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum, hsum]
      have hc : ((Icc 2 N).card : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.card_Icc, Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [hc]
      ring
    _ ≤ ∑ a ∈ Icc 2 N, ((R / a + 1 - (N + 1) : ℕ) : ℝ) := by
      apply sum_le_sum
      intro a ha
      exact fiber_cast_lower N R a (by have := (mem_Icc.mp ha).1; omega) (hd a ha)
    _ ≤ ((indexSupport R).card : ℝ) := by
      exact_mod_cast pair_count_le N R hNR

/-- A cofinal family of explicit cutoffs with an unbounded harmonic ratio. -/
theorem factorial_cutoff_lower (N : ℕ) (hN : 2 ≤ N) :
    let R : ℕ := N.factorial * (N+1)^2
    (R : ℝ) * ((harmonic N : ℝ) - 2) ≤ ((indexSupport R).card : ℝ) := by
  dsimp only
  let R : ℕ := N.factorial * (N+1)^2
  have hRsq : (N+1)^2 ≤ R := Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
  have hNR : N ≤ R := by nlinarith
  have hd : ∀ a ∈ Icc 2 N, a ∣ R := by
    intro a ha
    obtain ⟨ha2, haN⟩ := mem_Icc.mp ha
    exact dvd_mul_of_dvd_left (Nat.dvd_factorial (by omega) haN) _
  have hb := harmonic_lower N R hN hNR hd
  have hRsq' : ((N : ℝ)+1)^2 ≤ R := by exact_mod_cast hRsq
  change (R : ℝ) * ((harmonic N : ℝ) - 2) ≤ ((indexSupport R).card : ℝ)
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Arbitrary index-product supports have no uniform linear cardinality bound.
Distinct-prime product injectivity cannot be used for these supports. -/
theorem not_linear_support_bound :
    ¬ ∃ C : ℝ, ∀ R : ℕ, ((indexSupport R).card : ℝ) ≤ C * R := by
  rintro ⟨C, hC⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (max (Real.exp (C+2)) (2 : ℝ))
  have hN2 : 2 ≤ N := by
    have hh : (2 : ℝ) < N := (le_max_right _ _).trans_lt hN
    exact_mod_cast hh.le
  let R : ℕ := N.factorial * (N+1)^2
  have hR : 0 < R := Nat.mul_pos (Nat.factorial_pos _) (by positivity)
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hlog : C+2 < Real.log (N+1 : ℕ) := by
    apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
    have hh : Real.exp (C+2) < (N : ℝ) := (le_max_left _ _).trans_lt hN
    push_cast
    linarith
  have hharm := log_add_one_le_harmonic N
  have hlarge : C < (harmonic N : ℝ) - 2 := by linarith
  have hlo := factorial_cutoff_lower N hN2
  change (R : ℝ) * ((harmonic N : ℝ) - 2) ≤ ((indexSupport R).card : ℝ) at hlo
  have hup := hC R
  have hstrict := mul_lt_mul_of_pos_left hlarge hR'
  nlinarith

#print axioms not_linear_support_bound
end Erdos970.IndexSupportCost
