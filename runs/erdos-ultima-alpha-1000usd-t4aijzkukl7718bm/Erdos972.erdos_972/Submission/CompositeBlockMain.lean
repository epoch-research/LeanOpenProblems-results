import Submission.LargeDivisorBlockMain

/-! Removing prime outputs does not change the proved large-block first-moment
main term. This is a limitation of that particular statistic, not a disproof
of the prime-pair conjecture. -/
namespace Erdos972CompositeBlockMain

open Finset Filter
open scoped Topology
open Erdos972PrimePowerError Erdos972PrimeRoughOutputs Erdos972SelbergLowerTest
open Erdos972PolynomialRowScales Erdos972ChebyshevRowMean
open Erdos972ExplicitLargeDivisorBlock Erdos972LargeDivisorBlockMain

set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local irreducible] root64

noncomputable def nonPrimeOutputWeight (α : ℝ) (p : ℕ) : ℝ :=
  if (floorMul α p).Prime then 0 else primeWeight p

noncomputable def primeOutputBlockMass (α : ℝ) (N D : ℕ) : ℝ :=
  ∑ p ∈ Ioc 0 N,
    if (floorMul α p).Prime ∧ floorMul α p ∈ Ioc D (2*D)
    then primeWeight p else 0

lemma primeOutputBlockMass_nonneg (α : ℝ) (N D : ℕ) :
    0 ≤ primeOutputBlockMass α N D := by
  unfold primeOutputBlockMass
  apply sum_nonneg
  intro p hp
  split_ifs <;> first | exact primeWeight_nonneg p | exact le_rfl

lemma prime_block_divisor_sum {D q : ℕ} (hD : 0 < D) (hq : q.Prime) (a : ℝ) :
    (∑ d ∈ Ioc D (2*D), if d ∣ q then a else 0) =
      if q ∈ Ioc D (2*D) then a else 0 := by
  have he (d : ℕ) (hd : d ∈ Ioc D (2*D)) : d ∣ q ↔ d = q := by
    refine ⟨?_, fun h => h ▸ dvd_refl q⟩
    intro hdiv
    obtain h1 | hself := hq.eq_one_or_self_of_dvd d hdiv
    · have hDd := (mem_Ioc.mp hd).1
      omega
    · exact hself
  calc
    _ = ∑ d ∈ Ioc D (2*D), if d = q then a else 0 := by
      apply sum_congr rfl
      intro d hd
      simp only [he d hd]
    _ = _ := sum_ite_eq' _ _ _

/-- The difference counts each prime output in the block exactly once. -/
lemma block_firstMoment_prime_removal {D : ℕ} (hD : 0 < D) (α : ℝ) (N : ℕ) :
    (∑ d ∈ Ioc D (2*D), row (Ioc 0 N) primeWeight (floorMul α) d) -
      (∑ d ∈ Ioc D (2*D), row (Ioc 0 N) (nonPrimeOutputWeight α) (floorMul α) d) =
      primeOutputBlockMass α N D := by
  simp only [row, nonPrimeOutputWeight, ← sum_sub_distrib]
  rw [sum_comm]
  unfold primeOutputBlockMass
  apply sum_congr rfl
  intro p hp
  by_cases hq : (floorMul α p).Prime
  · simp only [hq, if_true, true_and, ite_self, sub_zero]
    exact prime_block_divisor_sum hD hq _
  · simp [hq]

/-- Prime outputs in (D,2D] come only from input primes at most 2D.
In particular their total logarithmic mass is O(D), uniformly in N. -/
lemma primeOutputBlockMass_le {α : ℝ} (hα : 1 ≤ α) (N D : ℕ) :
    primeOutputBlockMass α N D ≤ 14*(D:ℝ) := by
  classical
  have he : primeOutputBlockMass α N D =
      ∑ p ∈ (Ioc 0 N).filter
        (fun p => p.Prime ∧ (floorMul α p).Prime ∧ floorMul α p ∈ Ioc D (2*D)),
        Real.log p := by
    simp only [primeOutputBlockMass, primeWeight, sum_filter]
    apply sum_congr rfl
    intro p hp
    by_cases hpp : p.Prime <;>
      by_cases hq : (floorMul α p).Prime ∧ floorMul α p ∈ Ioc D (2*D) <;>
      simp [hpp, hq]
  have hθ : primeOutputBlockMass α N D ≤ Chebyshev.theta (2*D : ℕ) := by
    rw [he, Chebyshev.theta, Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpI, hpp, hqp, hqI⟩ := mem_filter.mp hp
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hpI).1, ?_⟩, hpp⟩
      exact (self_le_floorMul hα p).trans (mem_Ioc.mp hqI).2
    · intro p hp hnot
      exact Real.log_natCast_nonneg p
  have hb := (Chebyshev.theta_le_psi (2*D : ℕ)).trans
    (psi_le_seven_mul (Nat.cast_nonneg (2*D)))
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hb hθ
  linarith only [hθ, hb]

/-- The N log 2 main term persists even after every prime output is removed.
The same selected scale works for the original and restricted first moments. -/
theorem exists_nonPrimeOutput_block_firstMoment_log_two {α ε : ℝ}
    (hα : 1 < α) (hI : Irrational α) (hε : 0 < ε) (B : ℕ) :
    ∃ u D : ℕ, B < u ∧ 0 < u ∧ D = blockStart α (u^6) (root64 u) ∧
      0 < D ∧ D < u^6 ∧
      |(∑ d ∈ Ioc D (2*D), row (Ioc 0 (u^6)) primeWeight (floorMul α) d)-
        (u:ℝ)^6*Real.log 2| ≤ ε*(u:ℝ)^6 ∧
      |(∑ d ∈ Ioc D (2*D),
        row (Ioc 0 (u^6)) (nonPrimeOutputWeight α) (floorMul α) d)-
        (u:ℝ)^6*Real.log 2| ≤ ε*(u:ℝ)^6 ∧
      primeOutputBlockMass α (u^6) D ≤ ε*(u:ℝ)^6 := by
  let V := max (⌈α⌉₊+3) ⌈28*(α+1)/ε⌉₊
  obtain ⟨T, hT⟩ := eventually_atTop.mp (root64_tendsto.eventually_ge_atTop V)
  obtain ⟨u, D, hBu, hu, hDeq, hD, hDN, hfirst⟩ :=
    exists_block_firstMoment_log_two hα hI (show 0 < ε/2 by positivity) (max B T)
  have hVu := hT u ((le_max_right B T).trans hBu.le)
  have hvcut : ⌈α⌉₊+3 ≤ root64 u := (le_max_left _ _).trans hVu
  have hv0 := (root64_bounds hu).1
  have hv2 : 2 ≤ root64 u := by omega
  have hvu : root64 u ≤ u :=
    (Nat.le_self_pow (by decide : 64 ≠ 0) (root64 u)).trans (root64_bounds hu).2.1
  have hNv : root64 u ≤ u^6 := hvu.trans (Nat.le_self_pow (by decide : 6 ≠ 0) u)
  have hαv : α+1 < (root64 u:ℝ) := by
    have hh : (⌈α⌉₊:ℝ)+3 ≤ root64 u := by exact_mod_cast hvcut
    linarith only [hh, Nat.le_ceil α]
  obtain ⟨_, _, _, _, _, hDv⟩ :=
    blockStart_bounds hα.le hv0 hNv (root64_square_add_two_le_sixth hu hv2) hαv
  rw [← hDeq, Nat.cast_pow] at hDv
  have hbudget : 28*(α+1) ≤ ε*(root64 u:ℝ) := by
    have hceil : ⌈28*(α+1)/ε⌉₊ ≤ root64 u := (le_max_right _ _).trans hVu
    have hh := (Nat.le_ceil (28*(α+1)/ε)).trans (Nat.cast_le.mpr hceil)
    have hh' := (div_le_iff₀ hε).mp hh
    nlinarith only [hh']
  have hsmall : 14*(D:ℝ) ≤ (ε/2)*(u:ℝ)^6 := by
    have hvR : (0:ℝ) < root64 u := Nat.cast_pos.mpr hv0
    have h1 := mul_le_mul_of_nonneg_left hDv (show 0 ≤ (14:ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hbudget (show 0 ≤ (u:ℝ)^6 by positivity)
    nlinarith only [h1, h2, hvR]
  have hp := (primeOutputBlockMass_le hα.le (u^6) D).trans hsmall
  have hp0 := primeOutputBlockMass_nonneg α (u^6) D
  have he := block_firstMoment_prime_removal hD α (u^6)
  have hnonneg : 0 ≤ (u:ℝ)^6 := by positivity
  refine ⟨u, D, (le_max_left B T).trans_lt hBu, hu, hDeq, hD, hDN, ?_, ?_, ?_⟩
  · linarith only [hfirst, hε, hnonneg, mul_nonneg hε.le hnonneg]
  · rw [abs_le] at hfirst ⊢
    constructor <;> linarith only [hfirst.1, hfirst.2, he, hp, hp0,
      mul_nonneg hε.le hnonneg]
  · linarith only [hp, mul_nonneg hε.le hnonneg]

#print axioms block_firstMoment_prime_removal
#print axioms primeOutputBlockMass_le
#print axioms exists_nonPrimeOutput_block_firstMoment_log_two

end Erdos972CompositeBlockMain
