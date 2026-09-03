import Submission.FinitePrimeMass

/-! Quantitative reciprocal mass of the negative primes of a real quadratic
character, with any fixed initial segment removed. -/
namespace Erdos1206.QuadraticPrimePrefixBounds
open Finset Filter FinitePrimeMass RealQuadraticEulerMass
open scoped Topology Classical

lemma smoothing_tendsto :
    Tendsto (fun y : ℝ => 1+1/Real.log y) atTop (𝓝[>] 1) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have ht := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    simpa only [Function.comp_def,one_div,add_zero] using ht.const_add (1:ℝ)
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with y hy
    change 1 < 1+1/Real.log y
    have : 0 < 1/Real.log y := one_div_pos.mpr (Real.log_pos hy)
    linarith

lemma smoothing_cutoff {y : ℝ} (hy : 1 < y) : cutoff (1+1/Real.log y)=y := by
  rw [cutoff,add_sub_cancel_left,one_div_one_div,Real.exp_log (zero_lt_one.trans hy)]

theorem eventually_weighted_prefix_bounds {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℤ N) (hnc : complexChar χ ≠ 1)
    (hχ : ∀ n : ℕ, χ (n:ZMod N)=0 ∨ χ (n:ZMod N)=1 ∨ χ (n:ZMod N) = -1) :
    ∃ C D : ℝ, 0 < D ∧ ∀ᶠ y : ℝ in atTop,
      Real.log (Real.log y)-C ≤ ∑ p ∈ primePrefix y, (1-(χ (p:ZMod N):ℝ))/(p:ℝ) ∧
      (∑ p ∈ primePrefix y, Real.log (p:ℝ)/(p:ℝ)) ≤ D*Real.log y := by
  obtain ⟨C,D,hD,hbound⟩ := eventually_prefix_bounds χ hnc hχ
  refine ⟨C,D,hD,?_⟩
  filter_upwards [smoothing_tendsto.eventually hbound,eventually_gt_atTop (1:ℝ)] with y hy hy1
  rw [smoothing_cutoff hy1] at hy
  simp only [add_sub_cancel_left,one_div_one_div] at hy
  simpa only [one_div,div_inv_eq_mul] using hy

noncomputable def negativePrefix {N : ℕ} (χ : DirichletCharacter ℤ N) (H : ℕ) (y : ℝ) :
    Finset Nat.Primes := (primePrefix y).filter (fun p => H < (p:ℕ) ∧ χ (p:ZMod N) = -1)

lemma weighted_prefix_le_negative_head {N : ℕ} (χ : DirichletCharacter ℤ N)
    (hχ : ∀ n : ℕ, χ (n:ZMod N)=0 ∨ χ (n:ZMod N)=1 ∨ χ (n:ZMod N) = -1)
    (H : ℕ) (hreg : ∀ p : Nat.Primes, H < (p:ℕ) → χ (p:ZMod N) ≠ 0) (y : ℝ) :
    (∑ p ∈ primePrefix y, (1-(χ (p:ZMod N):ℝ))/(p:ℝ)) ≤
      2*(∑ p ∈ negativePrefix χ H y, 1/(p:ℝ))+
      2*(∑ p ∈ primePrefix (H:ℝ), 1/(p:ℝ)) := by
  have hlocal (p : Nat.Primes) : (1-(χ (p:ZMod N):ℝ))/(p:ℝ) ≤
      (if H < (p:ℕ) ∧ χ (p:ZMod N) = -1 then 2/(p:ℝ) else 0)+
      (if (p:ℕ) ≤ H then 2/(p:ℝ) else 0) := by
    by_cases hsmall : (p:ℕ) ≤ H
    · simp only [not_lt_of_ge hsmall,false_and,if_false,if_pos hsmall,zero_add]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hh := integer_abs_le_one (hχ p)
      have hl := neg_abs_le (χ (p:ZMod N):ℝ)
      linarith
    · have hlarge : H < (p:ℕ) := lt_of_not_ge hsmall
      rcases hχ p with hz | hone | hneg
      · exact (hreg p hlarge hz).elim
      · norm_num [hone,hlarge,hsmall]
      · norm_num [hneg,hlarge,hsmall]
  have hh := sum_le_sum (fun p (_ : p ∈ primePrefix y) => hlocal p)
  rw [sum_add_distrib,←sum_filter,←sum_filter] at hh
  have hhead : (primePrefix y).filter (fun p : Nat.Primes => (p:ℕ) ≤ H) ⊆ primePrefix (H:ℝ) := by
    intro p hp
    exact (mem_primePrefix (Nat.cast_nonneg H) p).mpr (by exact_mod_cast (mem_filter.mp hp).2)
  have hheadsum := sum_le_sum_of_subset_of_nonneg hhead
    (f := fun p : Nat.Primes => 2/(p:ℝ)) (fun p _ _ => by positivity)
  have he (P : Finset Nat.Primes) : (∑ p ∈ P, 2/(p:ℝ))=2*∑ p ∈ P, 1/(p:ℝ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  rw [he,he] at hh
  rw [he,he] at hheadsum
  dsimp only [negativePrefix]
  linarith

lemma negative_log_moment_le {N : ℕ} (χ : DirichletCharacter ℤ N) (H : ℕ) (y : ℝ) :
    (∑ p ∈ negativePrefix χ H y, Real.log (p:ℝ)/(p:ℝ)) ≤
      ∑ p ∈ primePrefix y, Real.log (p:ℝ)/(p:ℝ) := by
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  intro p _ _
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_le)) (by positivity)

/-- The negative primes have at least half of the logarithmic reciprocal mass,
up to a fixed additive constant. -/
theorem eventually_negative_prefix_bounds {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℤ N) (hnc : complexChar χ ≠ 1)
    (hχ : ∀ n : ℕ, χ (n:ZMod N)=0 ∨ χ (n:ZMod N)=1 ∨ χ (n:ZMod N) = -1)
    (H : ℕ) (hreg : ∀ p : Nat.Primes, H < (p:ℕ) → χ (p:ZMod N) ≠ 0) :
    ∃ C D : ℝ, 0 < D ∧ ∀ᶠ y : ℝ in atTop,
      (1/2)*Real.log (Real.log y)-C ≤ ∑ p ∈ negativePrefix χ H y, 1/(p:ℝ) ∧
      (∑ p ∈ negativePrefix χ H y, Real.log (p:ℝ)/(p:ℝ)) ≤ D*Real.log y := by
  obtain ⟨C,D,hD,hbound⟩ := eventually_weighted_prefix_bounds χ hnc hχ
  refine ⟨C/2+∑ p ∈ primePrefix (H:ℝ), 1/(p:ℝ),D,hD,?_⟩
  filter_upwards [hbound] with y hy
  have hhead := weighted_prefix_le_negative_head χ hχ H hreg y
  refine ⟨by linarith [hy.1],(negative_log_moment_le χ H y).trans hy.2⟩

#print axioms eventually_weighted_prefix_bounds
#print axioms weighted_prefix_le_negative_head
#print axioms eventually_negative_prefix_bounds
end Erdos1206.QuadraticPrimePrefixBounds
