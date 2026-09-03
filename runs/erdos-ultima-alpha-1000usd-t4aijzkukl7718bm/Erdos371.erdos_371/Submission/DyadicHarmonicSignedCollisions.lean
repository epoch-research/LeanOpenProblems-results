import Submission.PrimeWindowEnergyComparison
import Submission.PrimeLoserHarmonicDiagonal
import Submission.PrimeLoserPrimeWeightedCollisions

/-! An exact signed-collision expansion for the unnormalized fixed-window
critical energy. The off-diagonal term is not bounded here. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def dyadicLoserWindowDiagonal (N : ℕ) : ℝ :=
  ∑ n ∈ Ico N (2*N), primeLoserHarmonicDiagonal n

noncomputable def dyadicLoserWindowSignedCollisions (N : ℕ) : ℝ :=
  ∑ nm ∈ ((Ico N (2*N)).offDiag).filter (fun nm => primeLoser nm.1=primeLoser nm.2),
    (primeLoser nm.1 : ℝ)*(factorSign nm.1/nm.1)*(factorSign nm.2/nm.2)

lemma dyadicLoserWindowDiagonal_nonneg (N : ℕ) : 0≤dyadicLoserWindowDiagonal N := by
  unfold dyadicLoserWindowDiagonal
  exact sum_nonneg (fun n _ => primeLoserHarmonicDiagonal_nonneg n)

/-- The diagonal tends to zero by the already proved summability of
min(P(n),P(n+1))/n^2. No sign cancellation is used for this part. -/
theorem dyadicLoserWindowDiagonal_zero :
    Tendsto dyadicLoserWindowDiagonal atTop (𝓝 0) := by
  have ht := summable_primeLoserHarmonicDiagonal.hasSum.tendsto_sum_nat
  have hd : Tendsto (fun N : ℕ => 2*N) atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp; omega) tendsto_id
  have hs := (ht.comp hd).sub ht
  simp only [sub_self] at hs
  apply hs.congr
  intro N
  exact (sum_Ico_eq_sub primeLoserHarmonicDiagonal (show N≤2*N by omega)).symm

/-- All ordered off-diagonal collisions retain their actual product of
comparison signs and their reciprocal weights. -/
theorem dyadicPrimeLoserCriticalEnergy_collision_formula (N : ℕ) :
    dyadicPrimeLoserCriticalEnergy N = dyadicLoserWindowDiagonal N+
      dyadicLoserWindowSignedCollisions N := by
  let S := Ico N (2*N)
  let T := range (2*N+1)
  have hf : ∀ n∈S, primeLoser n∈T := by
    intro n hn
    have hnU := (mem_Ico.mp hn).2
    have hp : primeLoser n≤n :=
      (min_le_left (Nat.maxPrimeFac n) _).trans Nat.maxPrimeFac_le
    exact mem_range.mpr (by omega)
  have he : dyadicPrimeLoserCriticalEnergy N =
      ∑ p ∈ T, (p : ℝ)*(∑ n ∈ S.filter (fun n => primeLoser n=p), factorSign n/n)^2 := by
    unfold dyadicPrimeLoserCriticalEnergy
    simp only [primeLoserWindowCurrent_eq_sum_filter 2 N _ (by omega)]
    rfl
  rw [he,label_weighted_fiber_square_sum S T primeLoser
    (fun n => factorSign n/(n : ℝ)) (fun p => (p : ℝ)) hf,
    ← diag_union_offDiag,filter_union,
    sum_union (disjoint_filter_filter (disjoint_diag_offDiag S))]
  congr 1
  rw [filter_true_of_mem (fun nm hnm => congrArg primeLoser (mem_diag.mp hnm).2)]
  simp only [sum_diag,mul_assoc,← pow_two,div_pow,factorSign_sq,
    mul_one_div,dyadicLoserWindowDiagonal,primeLoserHarmonicDiagonal,S]

/-- This is an asymptotic identity, not cancellation of the collision sum. -/
theorem dyadicPrimeEnergy_sub_signedCollisions_zero :
    Tendsto (fun N => dyadicPrimeCriticalEnergy N-dyadicLoserWindowSignedCollisions N)
      atTop (𝓝 0) := by
  have ht := dyadicPrimeCriticalEnergy_difference_zero.add dyadicLoserWindowDiagonal_zero
  simp only [add_zero] at ht
  apply ht.congr
  intro N
  rw [dyadicPrimeLoserCriticalEnergy_collision_formula]
  ring

/-- Critical energy tends to zero exactly when this SIGNED, weighted
collision sum does. Neither limit is asserted unconditionally. -/
theorem dyadicPrimeEnergy_zero_iff_signedCollisions :
    Tendsto dyadicPrimeCriticalEnergy atTop (𝓝 0) ↔
      Tendsto dyadicLoserWindowSignedCollisions atTop (𝓝 0) := by
  constructor
  · intro h
    simpa only [sub_sub_cancel,sub_zero] using h.sub dyadicPrimeEnergy_sub_signedCollisions_zero
  · intro h
    simpa only [sub_add_cancel,add_zero] using dyadicPrimeEnergy_sub_signedCollisions_zero.add h

/-- Positivity supplies only this LOWER one-sided bound for the signed
cross term. It does not supply the missing upper bound. -/
theorem dyadicLoserWindowSignedCollisions_eventually_lower (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, -ε<dyadicLoserWindowSignedCollisions N := by
  filter_upwards [dyadicLoserWindowDiagonal_zero.eventually_lt_const hε] with N hN
  have he := dyadicPrimeLoserCriticalEnergy_nonneg N
  rw [dyadicPrimeLoserCriticalEnergy_collision_formula] at he
  linarith

/-- A one-sided arithmetic estimate for the signed repeated-label terms
would suffice for the ORIGINAL conjecture. This estimate is still unproved. -/
theorem density_of_dyadicSignedCollisions_limsup
    (h : ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
      dyadicLoserWindowSignedCollisions N≤ε) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) := by
  apply density_of_dyadicPrimeCriticalEnergy
  apply dyadicPrimeEnergy_zero_iff_signedCollisions.mpr
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have he : 0< -a := by linarith
    simpa only [neg_neg] using dyadicLoserWindowSignedCollisions_eventually_lower (-a) he
  · intro a ha
    filter_upwards [h (a/2) (by positivity)] with N hN
    linarith

#print axioms dyadicPrimeLoserCriticalEnergy_collision_formula
#print axioms dyadicPrimeEnergy_sub_signedCollisions_zero
#print axioms density_of_dyadicSignedCollisions_limsup
end Erdos371
