import Submission.PrimePatternApproximation

/-! Uniform factorial moments for the two-colour prime pattern. These also
control tails of polynomially growing local observables. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

/-- The first L inclusion degrees give a factorial-moment bound without
assuming independence of the natural-prefix sample. -/
theorem prime_pattern_factorial_moment_bound (P : Finset ℕ) (hP : ∀ p∈P, p.Prime)
    (N L : ℕ) (hN : 0<N) (Z : ℝ) (hZ : 1≤Z)
    (hsum : (∑ a ∈ primeAtoms P, 2*(a.1 : ℝ))≤Z) :
    (∑ n ∈ range N, ((activePrimeAtoms P n).card.choose L : ℝ))/N ≤
      (2*∑ p ∈ P, (1 : ℝ)/p)^L/L.factorial+Z^L/N := by
  have he := pattern_factorial_moment (primeAtoms P) L (range N) (fun _ => (1 : ℝ)/N)
    (activePrimeAtoms P) (fun n _ => activePrimeAtoms_subset P n)
  have hs : (∑ n ∈ range N, (1 : ℝ)/N*((activePrimeAtoms P n).card.choose L)) =
      (∑ n ∈ range N, ((activePrimeAtoms P n).card.choose L : ℝ))/N := by
    rw [← mul_sum]
    ring
  rw [hs] at he
  rw [he]
  calc
    _ ≤ ∑ T ∈ (primeAtoms P).powersetCard L,
        (primeAtomModel T+(∏ a ∈ T, (a.1 : ℝ))/N) := by
      apply sum_le_sum
      intro T hT
      have h := prime_pattern_inclusion_error P hP N hN T (mem_powersetCard.mp hT).1
      have hh := (le_abs_self (patternInclusionMass (range N) (fun _ => (1 : ℝ)/N) (activePrimeAtoms P) T-
        primeAtomModel T)).trans h
      linarith
    _ ≤ (2*∑ p ∈ P, (1 : ℝ)/p)^L/L.factorial+Z^L/N := by
      rw [sum_add_distrib]
      apply add_le_add _ (prime_pattern_rounding_moment P N L Z hZ hsum)
      calc
        _ ≤ ∑ T ∈ (primeAtoms P).powersetCard L, ∏ a ∈ T, (1 : ℝ)/a.1 :=
          sum_le_sum fun T _ => primeAtomModel_le T
        _ ≤ (∑ a ∈ primeAtoms P, (1 : ℝ)/a.1)^L/L.factorial :=
          elementarySum_le_pow_div_factorial _ _ (fun _ _ => by positivity) L
        _ = _ := by rw [primeAtom_reciprocal_sum]

/-- A simple explicit exponent suffices for any one prescribed moment.
Uniformity includes all prime sets below that power and with the mass bound. -/
theorem prime_pattern_factorial_moment_small_power (L : ℕ) (M ε : ℝ)
    (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ P : Finset ℕ,
      (∀ p∈P, p.Prime ∧ (p : ℝ)≤(N : ℝ)^(1/(4*(L+1 : ℝ)))) →
      (2*∑ p∈P, (1 : ℝ)/p)≤M →
      (∑ n∈range N, ((activePrimeAtoms P n).card.choose L : ℝ))/N≤M^L/L.factorial+ε := by
  let δ : ℝ := 1/(4*(L+1 : ℝ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have ht : Tendsto (fun N : ℕ => (16 : ℝ)^(L+1)*(N : ℝ)^(-(1/2 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/2)).comp tendsto_natCast_atTop_atTop).const_mul ((16 : ℝ)^(L+1))
  filter_upwards [eventually_ge_atTop (1 : ℕ),ht.eventually_lt_const hε] with N hN hsmall
  intro P hP hmass
  have hNr : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
  let X : ℕ := ⌊(N : ℝ)^δ⌋₊
  let Z : ℝ := 4*(X+1 : ℝ)^2
  have hX : (X : ℝ)≤(N : ℝ)^δ := Nat.floor_le (Real.rpow_nonneg hNr.le δ)
  have hpow1 : (1 : ℝ)≤(N : ℝ)^δ := Real.one_le_rpow hN1 hδ.le
  have hZ : 1≤Z := by dsimp [Z]; nlinarith [Nat.cast_nonneg (α := ℝ) X]
  have hZupper : Z≤16*((N : ℝ)^δ)^2 := by
    dsimp [Z]
    nlinarith [sq_nonneg ((N : ℝ)^δ-X),Nat.cast_nonneg (α := ℝ) X]
  have hpow : (((N : ℝ)^δ)^2)^(L+1)=(N : ℝ)^(1/2 : ℝ) := by
    rw [← pow_mul,← Real.rpow_natCast,← Real.rpow_mul hNr.le]
    congr 1
    dsimp [δ]
    push_cast
    field_simp
    ring
  have hround : Z^L/N≤(16 : ℝ)^(L+1)*(N : ℝ)^(-(1/2 : ℝ)) := by
    calc
      _ ≤ Z^(L+1)/N := div_le_div_of_nonneg_right (pow_le_pow_right₀ hZ (by omega)) hNr.le
      _ ≤ (16*((N : ℝ)^δ)^2)^(L+1)/N :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (by linarith) hZupper _) hNr.le
      _ = _ := by
        rw [mul_pow,hpow,show -(1/2 : ℝ)=1/2-1 by ring,Real.rpow_sub hNr,Real.rpow_one]
        ring
  have hm := prime_pattern_factorial_moment_bound P (fun p hp => (hP p hp).1) N L (by omega) Z hZ
    (prime_atoms_modulus_budget P X (fun p hp => (Nat.le_floor_iff (by positivity)).mpr (hP p hp).2))
  have hmain : (2*∑ p∈P, (1 : ℝ)/p)^L/L.factorial≤M^L/L.factorial := by
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hmass _) (Nat.cast_nonneg _)
  linarith

#print axioms prime_pattern_factorial_moment_small_power
end Erdos371.FiniteSieve
