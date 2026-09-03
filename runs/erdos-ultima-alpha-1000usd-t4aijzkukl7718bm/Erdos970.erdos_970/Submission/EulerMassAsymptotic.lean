import Submission.EulerMassNineFifths
import Submission.PrimeSetMertens

/-! An elementary Mertens-product asymptotic with an unspecified positive
constant. Its identification with exp(Euler's constant) is not needed here.
The proof uses only the already established reciprocal-prime interval error. -/
namespace Erdos970.FiniteSelberg
open Finset Real Filter
open scoped Topology

noncomputable def initialEulerMass (n : ℕ) : ℝ := eulerMass (n+1).primesBelow

lemma initialEulerMass_pos (n : ℕ) : 0 < initialEulerMass n := by
  unfold initialEulerMass eulerMass
  apply prod_pos
  intro p hp
  have hh : (1 : ℝ) < p := by exact_mod_cast (WeightedMertens.mem_primes.mp hp).1.one_lt
  have hq : 1/(p : ℝ) < 1 := (div_lt_one (by linarith)).mpr hh
  exact inv_pos.mpr (by linarith)

lemma log_euler_factor_error (p : ℕ) (hp : p.Prime) :
    0 ≤ -log (1-1/(p : ℝ))-1/(p : ℝ) ∧
      -log (1-1/(p : ℝ))-1/(p : ℝ) ≤ 1/((p : ℝ)*(p-1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hq : (0 : ℝ) < 1-1/(p : ℝ) := by
    apply sub_pos.mpr
    exact (div_lt_one hp0).mpr hp1
  constructor
  · have hh := log_le_sub_one_of_pos hq
    linarith
  · have hh := log_le_sub_one_of_pos (inv_pos.mpr hq)
    rw [log_inv] at hh
    have he : (1-1/(p : ℝ))⁻¹-1-1/(p : ℝ) = 1/((p : ℝ)*(p-1)) := by
      have hm : (p : ℝ)-1 ≠ 0 := by linarith
      rw [show 1-1/(p : ℝ) = ((p : ℝ)-1)/p by field_simp, inv_div]
      field_simp [hp0.ne',hm]
      <;> ring
    linarith

lemma correction_Ioc_sum (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
    (∑ p ∈ Ioc m n, 1/((p : ℝ)*(p-1))) = 1/(m : ℝ)-1/(n : ℝ) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [sum_Ioc_succ_top hmn, ih]
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hn1 : (n+1 : ℝ) ≠ 0 := by positivity
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    field_simp [hn,hn1,hm0]
    <;> ring

lemma log_initialEulerMass (n : ℕ) : log (initialEulerMass n) =
    ∑ p ∈ (n+1).primesBelow, -log (1-1/(p : ℝ)) := by
  rw [initialEulerMass, eulerMass, log_prod]
  · simp only [log_inv]
  · intro p hp
    have hh : (1 : ℝ) < p := by exact_mod_cast (WeightedMertens.mem_primes.mp hp).1.one_lt
    have hq : 1/(p : ℝ) < 1 := (div_lt_one (by linarith)).mpr hh
    exact inv_ne_zero (by linarith)

lemma initial_prime_sum_difference (f : ℕ → ℝ) (m n : ℕ) (hmn : m ≤ n) :
    (∑ p ∈ (n+1).primesBelow, f p)-(∑ p ∈ (m+1).primesBelow, f p) =
      ∑ p ∈ (Ioc m n).filter Nat.Prime, f p := by
  have hsub : (m+1).primesBelow ⊆ (n+1).primesBelow := by
    intro p hp
    obtain ⟨hpp,hpm⟩ := WeightedMertens.mem_primes.mp hp
    exact WeightedMertens.mem_primes.mpr ⟨hpp,hpm.trans hmn⟩
  have he : (n+1).primesBelow \ (m+1).primesBelow = (Ioc m n).filter Nat.Prime := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpn,hpm⟩ := mem_sdiff.mp hp
      obtain ⟨hpp,hpn⟩ := WeightedMertens.mem_primes.mp hpn
      have hpm' : m < p := by
        by_contra h
        exact hpm (WeightedMertens.mem_primes.mpr ⟨hpp,by omega⟩)
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpm',hpn⟩,hpp⟩
    · intro hp
      obtain ⟨hpI,hpp⟩ := mem_filter.mp hp
      obtain ⟨hpm,hpn⟩ := mem_Ioc.mp hpI
      exact mem_sdiff.mpr ⟨WeightedMertens.mem_primes.mpr ⟨hpp,hpn⟩,
        fun h => (not_le_of_gt hpm) (WeightedMertens.mem_primes.mp h).2⟩
  rw [← sum_sdiff hsub, he]
  ring

noncomputable def eulerLogPhase (n : ℕ) : ℝ := log (initialEulerMass n)-log (log (n : ℝ))

/-- A Cauchy modulus for the logarithmically normalized Euler product. -/
theorem eulerLogPhase_difference (m n : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    |eulerLogPhase n-eulerLogPhase m| ≤
      2*(WeightedMertens.boundConstant+1)/log (m : ℝ)+1/(m : ℝ) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hr := WeightedMertens.abs_reciprocalInterval_sub_loglog hmR hmnR
  simp only [WeightedMertens.reciprocalInterval, Nat.floor_natCast] at hr
  let Q := (Ioc m n).filter Nat.Prime
  let c (p : ℕ) : ℝ := -log (1-1/(p : ℝ))-1/(p : ℝ)
  have hc0 : 0 ≤ ∑ p ∈ Q, c p := by
    apply sum_nonneg
    intro p hp
    exact (log_euler_factor_error p (mem_filter.mp hp).2).1
  have hc1 : (∑ p ∈ Q, c p) ≤ 1/(m : ℝ) := by
    calc
      _ ≤ ∑ p ∈ Q, 1/((p : ℝ)*(p-1)) := sum_le_sum (fun p hp =>
        (log_euler_factor_error p (mem_filter.mp hp).2).2)
      _ ≤ ∑ p ∈ Ioc m n, 1/((p : ℝ)*(p-1)) := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro p hp hnot
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by have := (mem_Ioc.mp hp).1; omega)
        exact div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg p) (sub_nonneg.mpr hp1))
      _ = 1/(m : ℝ)-1/(n : ℝ) := correction_Ioc_sum m n (by omega) hmn
      _ ≤ _ := by
        have hh : (0 : ℝ) ≤ 1/(n : ℝ) := by positivity
        linarith
  have he : eulerLogPhase n-eulerLogPhase m =
      ((∑ p ∈ Q, (p : ℝ)⁻¹)-(log (log (n : ℝ))-log (log (m : ℝ))))+
        ∑ p ∈ Q, c p := by
    unfold eulerLogPhase
    rw [log_initialEulerMass, log_initialEulerMass]
    have hh := initial_prime_sum_difference (fun p => -log (1-1/(p : ℝ))) m n hmn
    dsimp only [Q,c]
    rw [sum_sub_distrib]
    simp only [one_div] at hh ⊢
    linarith only [hh]
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_of_nonneg hc0]
  exact add_le_add hr hc1

lemma eulerLogPhase_cauchy : CauchySeq eulerLogPhase := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop := tendsto_log_atTop.comp hnat
  have he : Tendsto (fun n : ℕ => 2*(WeightedMertens.boundConstant+1)/log (n : ℝ)+1/(n : ℝ))
      atTop (𝓝 0) := by
    simpa using (hlog.const_div_atTop (2*(WeightedMertens.boundConstant+1))).add (hnat.const_div_atTop 1)
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (he.eventually_lt_const hε)
  refine ⟨max N 2, fun n hn => ?_⟩
  rw [Real.dist_eq]
  exact (eulerLogPhase_difference (max N 2) n (le_max_right _ _) hn).trans_lt
    (hN (max N 2) (le_max_left _ _))

/-- Existence of the positive Mertens-product constant, without identifying it. -/
theorem exists_initialEulerMass_log_limit : ∃ C > (0 : ℝ),
    Tendsto (fun n : ℕ => initialEulerMass n/log (n : ℝ)) atTop (𝓝 C) := by
  obtain ⟨c,hc⟩ := cauchySeq_tendsto_of_complete eulerLogPhase_cauchy
  refine ⟨exp c, exp_pos c, ?_⟩
  have he : Tendsto (fun n => exp (eulerLogPhase n)) atTop (𝓝 (exp c)) :=
    (continuous_exp.tendsto c).comp hc
  apply he.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hl : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  simp only [eulerLogPhase, exp_sub, exp_log (initialEulerMass_pos n), exp_log hl]

#print axioms eulerLogPhase_difference
#print axioms exists_initialEulerMass_log_limit
end Erdos970.FiniteSelberg
