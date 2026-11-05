import Mathlib

/-! An elementary small Euler-product density, from the kernel-proved divergence
of the reciprocals of the primes. No Mertens or prime-number theorem is assumed. -/

open Filter
open scoped BigOperators Topology

namespace Erdos5EfficientCover

/-- The proportion left by one residue class at every prime at most `P`. -/
noncomputable def primeDensity (P : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesBelow (P + 1), (1 - 1 / (p : ℝ))

theorem primeDensity_nonneg (P : ℕ) : 0 ≤ primeDensity P := by
  apply Finset.prod_nonneg
  intro p hp
  have hp' := Nat.prime_of_mem_primesBelow hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp'.one_le
  exact sub_nonneg.mpr ((div_le_one hp0).mpr hp1)

/-- The finite Euler product is dominated by the exponential of minus the prime harmonic sum. -/
theorem primeDensity_le_exp (P : ℕ) :
    primeDensity P ≤ Real.exp (-∑ p ∈ Nat.primesBelow (P + 1), (1 / p : ℝ)) := by
  unfold primeDensity
  calc
    (∏ p ∈ Nat.primesBelow (P + 1), (1 - 1 / (p : ℝ))) ≤
        ∏ p ∈ Nat.primesBelow (P + 1), Real.exp (-(1 / p : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp' := Nat.prime_of_mem_primesBelow hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.pos
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp'.one_le
        exact sub_nonneg.mpr ((div_le_one hp0).mpr hp1)
      · intro p _
        exact Real.one_sub_le_exp_neg _
    _ = Real.exp (-∑ p ∈ Nat.primesBelow (P + 1), (1 / p : ℝ)) := by
      rw [← Real.exp_sum, Finset.sum_neg_distrib]

/-- The inclusive finite prime harmonic sums tend to infinity. -/
theorem tendsto_prime_harmonic_sum :
    Tendsto (fun P : ℕ => ∑ p ∈ Nat.primesBelow (P + 1), (1 / p : ℝ)) atTop atTop := by
  have hnonneg : ∀ n : ℕ,
      0 ≤ Set.indicator {p : ℕ | p.Prime} (fun p => (1 / p : ℝ)) n :=
    fun n => Set.indicator_nonneg (fun p _ => by positivity) n
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp
    not_summable_one_div_on_primes
  have heq : (fun N : ℕ => ∑ p ∈ Finset.range N,
        Set.indicator {p : ℕ | p.Prime} (fun p => (1 / p : ℝ)) p) =
      (fun N : ℕ => ∑ p ∈ Nat.primesBelow N, (1 / p : ℝ)) := by
    funext N
    simp [Nat.primesBelow, Finset.sum_filter, Set.indicator]
  rw [heq] at hdiv
  exact hdiv.comp (tendsto_add_atTop_nat 1)

/-- One can make the product of the local surviving proportions arbitrarily small. -/
theorem exists_primeDensity_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, primeDensity P < ε := by
  have hexp : Tendsto (fun P : ℕ =>
      Real.exp (-∑ p ∈ Nat.primesBelow (P + 1), (1 / p : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_prime_harmonic_sum
  obtain ⟨P, hP⟩ := (hexp.eventually (gt_mem_nhds hε)).exists
  exact ⟨P, (primeDensity_le_exp P).trans_lt hP⟩

end Erdos5EfficientCover

#print axioms Erdos5EfficientCover.tendsto_prime_harmonic_sum
#print axioms Erdos5EfficientCover.exists_primeDensity_lt
