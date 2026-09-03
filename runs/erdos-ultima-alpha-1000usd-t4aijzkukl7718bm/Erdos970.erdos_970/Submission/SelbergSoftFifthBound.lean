import Submission.SelbergSoftPrimeBound
import Submission.PrimeSecondLogMoment

/-! An improved positive soft-profile bound. The exponent is five, not two. -/
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma softProfile_energy_fifth (q u : ι → ℝ)
    (hq : ∀ i, 0 < q i ∧ q i < 1) (hu : ∀ i, 0 ≤ u i)
    (M : ℝ) (hM : 0 < M)
    (hmean : (∑ i, q i * u i) ≤ (65 / 64) * M)
    (hsecond : (∑ i, q i * u i ^ 2) ≤ (49 / 64) * M ^ 2) :
    M ^ 2 / 8 ≤ kernelEnergy q (fun Q => weight q Q * softProfile u (2 * M) Q) := by
  have hh := softProfile_energy_lower q u hq hu (2 * M) ((65 / 64) * M)
    ((49 / 64) * M ^ 2) (by linarith) hmean hsecond
  have hW := one_le_sum_weight q hq
  have hcoef : M ^ 2 / 8 ≤ (2 * M - (65 / 64) * M) ^ 2 - (49 / 64) * M ^ 2 := by
    nlinarith [sq_nonneg M]
  have hcoef0 := (by positivity : 0 ≤ M ^ 2 / 8).trans hcoef
  have hmul := mul_le_mul_of_nonneg_right hW hcoef0
  nlinarith only [hh, hcoef, hmul]

noncomputable def fifthBoundConstant : ℝ := 32 * exp (4 + 4 * WeightedMertens.logMomentOffset) * 64 ^ 4

lemma fifthBoundConstant_pos : 0 < fifthBoundConstant := by unfold fifthBoundConstant; positivity

/-- Positive energy and a controlled cost, uniformly over all prime sets with
at most k members. There is no upper-size restriction on their primes. -/
theorem exists_soft_prime_kernel_fifth (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (k : ℕ) (hcard : Fintype.card ι ≤ k) :
    ∃ c : Finset ι → ℝ, 0 < kernelEnergy (fun i => 1 / (p i : ℝ)) c ∧
      (Fintype.card ι + 1 : ℝ) * kernelCost (fun i => 1 / (p i : ℝ)) c ^ 2 ≤
        fifthBoundConstant * ((k : ℝ) + 1) ^ 5 * kernelEnergy (fun i => 1 / (p i : ℝ)) c := by
  classical
  let P := univ.image p
  let z : ℕ := 64 * (k + 1)
  let M := log (z : ℝ) + WeightedMertens.logMomentOffset
  let L := (2 : ℝ) * M
  let q := fun i => 1 / (p i : ℝ)
  let u := fun i => log (p i : ℝ)
  let c := fun Q => weight q Q * softProfile u L Q
  have hP : ∀ a ∈ P, a.Prime := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    exact hp i
  have hPcard : P.card ≤ k := by
    exact (card_image_le.trans_eq (card_univ : (univ : Finset ι).card = Fintype.card ι)).trans hcard
  have hz : 64 ≤ z := by dsimp [z]; omega
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hM : 0 < M := by
    have hh := WeightedMertens.two_le_log_of_sixty_four_le (z := (z : ℝ)) (by exact_mod_cast hz)
    have hb := WeightedMertens.logMomentOffset_pos
    dsimp [M]; linarith
  have hmom := WeightedMertens.prime_log_moments_improved P hP z hz (by dsimp [z]; omega)
  dsimp only [P] at hmom
  rw [sum_image hinj.injOn, sum_image hinj.injOn] at hmom
  have henergy : M ^ 2 / 8 ≤ kernelEnergy q c := by
    apply softProfile_energy_fifth q u (prime_marginals p hp)
      (fun i => log_nonneg (by exact_mod_cast (hp i).one_le)) M hM
    · simpa [q, u, M, div_eq_mul_inv, mul_comm] using hmom.1
    · simpa [q, u, M, div_eq_mul_inv, mul_comm] using hmom.2
  have hL : 0 < L := by dsimp [L]; positivity
  have hcost : kernelCost q c ≤ L * exp 2 * exp L := prime_soft_cost_le p hp hinj L hL.le
  have hcost0 : 0 ≤ kernelCost q c := sum_nonneg (fun _ _ => abs_nonneg _)
  have hexp : exp (2 * L) = exp (4 * WeightedMertens.logMomentOffset) * (z : ℝ) ^ 4 := by
    have he : 2 * L = 4 * WeightedMertens.logMomentOffset + log ((z : ℝ) ^ 4) := by
      rw [log_pow]
      dsimp [L, M]
      norm_num
      ring
    rw [he, exp_add, exp_log (by positivity)]
  have hcostsq : kernelCost q c ^ 2 ≤
      4 * M ^ 2 * exp (4 + 4 * WeightedMertens.logMomentOffset) * (z : ℝ) ^ 4 := by
    have hh := (sq_le_sq₀ hcost0 (by positivity : 0 ≤ L * exp 2 * exp L)).mpr hcost
    have he : (L * exp 2 * exp L) ^ 2 = L ^ 2 * exp 4 * exp (2 * L) := by
      rw [mul_pow, mul_pow, ← exp_nat_mul, ← exp_nat_mul]
      norm_num
    rw [he, hexp] at hh
    rw [exp_add]
    dsimp [L] at hh
    nlinarith only [hh]
  refine ⟨c, lt_of_lt_of_le (by positivity : 0 < M ^ 2 / 8) henergy, ?_⟩
  have hc : (Fintype.card ι + 1 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hcard 1
  calc
    _ ≤ ((k : ℝ) + 1) * kernelCost q c ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ ≤ ((k : ℝ) + 1) * (4 * M ^ 2 * exp (4 + 4 * WeightedMertens.logMomentOffset) * (z : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hcostsq (by positivity)
    _ = fifthBoundConstant * ((k : ℝ) + 1) ^ 5 * (M ^ 2 / 8) := by
      dsimp [fifthBoundConstant, z]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left henergy
      (mul_nonneg fifthBoundConstant_pos.le (by positivity))

/-- An unconditional prime-class survivor bound with a fifth-power threshold. -/
theorem prime_survivor_soft_fifth (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (k : ℕ) (hcard : Fintype.card ι ≤ k)
    (r : ℕ → ℕ) (m : ℕ)
    (hm : fifthBoundConstant * ((k : ℝ) + 1) ^ 5 < m) :
    ∃ j < m, ∀ i, ¬j ≡ r (p i) [MOD p i] := by
  obtain ⟨c, he, hc⟩ := exists_soft_prime_kernel_fifth p hp hinj k hcard
  have hh := survivor_of_kernelEnergy (fun i => 1 / (p i : ℝ))
    (fun i => (prime_marginals p hp i).1.ne') c m
    (fun j i => decide (j ≡ r (p i) [MOD p i]))
    (prime_hits_intersection_error p hp hinj r m)
    (hc.trans_lt (mul_lt_mul_of_pos_right hm he))
  simpa using hh

#print axioms exists_soft_prime_kernel_fifth
#print axioms prime_survivor_soft_fifth
end Erdos970.FiniteSelberg
