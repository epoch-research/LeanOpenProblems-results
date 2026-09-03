import Submission.PrimeFejer
import Submission.PrimeDirichletPole

/-!
Finite weighted Fejér energies for ratios of primes. This development is separate
from the unresolved assertion for every prescribed irrational slope.
-/
namespace Erdos972PrimeRatioKernel

open Finset Complex
open scoped ComplexConjugate
open Erdos972ExponentialSum Erdos972PrimeFejer Erdos972LogPrimeBlocks
open Erdos972PrimeDirichletPole

noncomputable def weightedExpSum (S : Finset ℕ) (w x : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ p ∈ S, (w p : ℂ) * phase (t * x p)

noncomputable def pairEnergy (S : Finset ℕ) (w x : ℕ → ℝ) (c D : ℝ) (H : ℕ) : ℝ :=
  ∑ z ∈ S ×ˢ S, w z.1 * w z.2 * ‖dirichletKernel H ((x z.2 - x z.1 - c) / D)‖ ^ 2

lemma pair_phase_sum (S : Finset ℕ) (w x : ℕ → ℝ) (t c : ℝ) :
    (∑ p ∈ S, ∑ q ∈ S, ((w p * w q : ℝ) : ℂ) * phase (t * (x q - x p - c))) =
      phase (-t * c) * ((‖weightedExpSum S w x t‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [weightedExpSum, map_sum, map_mul, Complex.conj_ofReal, conjugate_phase,
    mul_sum, sum_mul]
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro p hp
  rw [show t * (x p - x q - c) = (-t * c + t * x p) + -(t * x q) by ring,
    phase_add, phase_add, Complex.ofReal_mul]
  ring

lemma pairEnergy_fourier (S : Finset ℕ) (w x : ℕ → ℝ) (c D : ℝ) (H : ℕ) :
    pairEnergy S w x c D H =
      ∑ i ∈ range H, ∑ j ∈ range H,
        (phase (-((i : ℝ) - j) / D * c)).re *
          ‖weightedExpSum S w x (((i : ℝ) - j) / D)‖ ^ 2 := by
  have he : (pairEnergy S w x c D H : ℂ) =
      ∑ i ∈ range H, ∑ j ∈ range H,
        phase (-((i : ℝ) - j) / D * c) *
          ((‖weightedExpSum S w x (((i : ℝ) - j) / D)‖ ^ 2 : ℝ) : ℂ) := by
    unfold pairEnergy
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, dirichletKernel_energy, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    rw [sum_product]
    have hf := pair_phase_sum S w x (((i : ℝ) - j) / D) c
    convert hf using 1
    · apply sum_congr rfl
      intro p hp
      apply sum_congr rfl
      intro q hq
      push_cast
      congr 2
      ring
    · congr 2
      ring
  have hr := congrArg Complex.re he
  simpa only [Complex.ofReal_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_im, mul_zero,
    sub_zero] using hr

/-- A band of positive entries dominates a matrix whose remaining entries are
bounded below. This avoids having to evaluate the full triangular Fourier sum. -/
lemma matrix_band_lower (H u : ℕ) (A : ℕ → ℕ → ℝ) (a E : ℝ)
    (hE : 0 ≤ E)
    (hlower : ∀ i < H, ∀ j < H, -E ≤ A i j)
    (hband : ∀ i < H - u, ∀ j ∈ Ioc i (i + u), a ≤ A i j) :
    ((H - u : ℕ) : ℝ) * u * a - (H : ℝ) ^ 2 * E ≤
      ∑ i ∈ range H, ∑ j ∈ range H, A i j := by
  have hrow (i : ℕ) (hi : i < H - u) :
      (u : ℝ) * a ≤ ∑ j ∈ range H, (A i j + E) := by
    have hsub : Ioc i (i + u) ⊆ range H := by
      intro j hj
      simp only [mem_Ioc, mem_range] at *
      omega
    calc
      _ = ∑ j ∈ Ioc i (i + u), a := by simp
      _ ≤ ∑ j ∈ Ioc i (i + u), (A i j + E) := by
        apply sum_le_sum
        intro j hj
        linarith [hband i hi j hj]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => by
        have hiH : i < H := by omega
        have hh := hlower i hiH j (mem_range.mp hj)
        linarith)
  have hall (i : ℕ) (hi : i ∈ range H) : 0 ≤ ∑ j ∈ range H, (A i j + E) := by
    apply sum_nonneg
    intro j hj
    linarith [hlower i (mem_range.mp hi) j (mem_range.mp hj)]
  have hsum : ((H - u : ℕ) : ℝ) * u * a ≤
      ∑ i ∈ range H, ∑ j ∈ range H, (A i j + E) := by
    calc
      _ = ∑ i ∈ range (H - u), (u : ℝ) * a := by simp; ring
      _ ≤ ∑ i ∈ range (H - u), ∑ j ∈ range H, (A i j + E) :=
        sum_le_sum (fun i hi => hrow i (mem_range.mp hi))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le H u))
        (fun i hi _ => hall i hi)
  simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at hsum
  nlinarith

lemma inv_sq_le_lorentz {x δ : ℝ} (hδ : 0 < δ) (hx : δ ≤ |x|) :
    1 / x ^ 2 ≤ (1 + 1 / δ ^ 2) / (1 + x ^ 2) := by
  have hx0 : x ≠ 0 := by intro he; simp [he] at hx; linarith
  have hsq : δ ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x]
  have hh : 1 ≤ x ^ 2 / δ ^ 2 := (le_div_iff₀ (sq_pos_of_pos hδ)).mpr (by simpa using hsq)
  apply (div_le_div_iff₀ (sq_pos_of_ne_zero hx0) (by positivity)).mpr
  have he : (1 + 1 / δ ^ 2) * x ^ 2 = x ^ 2 + x ^ 2 / δ ^ 2 := by ring
  rw [he]
  linarith

lemma kernel_sq_le_lorentz (H : ℕ) {D x δ : ℝ} (hD : 0 < D)
    (hδ : 0 < δ) (hx : δ ≤ |x|) (hhalf : |x| ≤ D / 2) :
    ‖dirichletKernel H (x / D)‖ ^ 2 ≤
      D ^ 2 * ((1 + 1 / δ ^ 2) / (1 + x ^ 2)) := by
  have hax : 0 < |x| := hδ.trans_le hx
  have ht : |x / D| ≤ 1 / 2 := by rw [abs_div, abs_of_pos hD]; exact (div_le_iff₀ hD).mpr (by linarith)
  have hl := four_mul_le_norm_phase_sub_one (abs_nonneg (x / D)) ht
  rw [norm_phase_abs_sub_one, abs_div, abs_of_pos hD] at hl
  have hg := norm_dirichletKernel_mul_le H (x / D)
  have hp := mul_le_mul_of_nonneg_left hl (norm_nonneg (dirichletKernel H (x / D)))
  have he : ‖dirichletKernel H (x / D)‖ * (4 * (|x| / D)) =
      (4 * ‖dirichletKernel H (x / D)‖ * |x|) / D := by ring
  rw [he] at hp
  have hmul := (div_le_iff₀ hD).mp (hp.trans hg)
  have hnorm : ‖dirichletKernel H (x / D)‖ ≤ D / |x| := by
    apply (le_div_iff₀ hax).mpr
    nlinarith
  have hs := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [div_pow, sq_abs] at hs
  calc
    _ ≤ D ^ 2 / x ^ 2 := hs
    _ = D ^ 2 * (1 / x ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (inv_sq_le_lorentz hδ hx) (sq_nonneg D)

noncomputable def rowConstant (δ : ℝ) : ℝ :=
  (1 + 1 / δ ^ 2) * (3 * (Real.exp 1 * Real.log 4) * lorentzMass)

lemma rowConstant_nonneg (δ : ℝ) : 0 ≤ rowConstant δ := by
  unfold rowConstant
  have := lorentzMass_nonneg
  positivity

/-- A missing log-ratio interval gives a kernel-energy upper bound independent
of the number of frequencies. -/
theorem pairEnergy_upper_of_avoids {ε D δ c : ℝ} (hε : 0 ≤ ε) (hD : 0 < D)
    (hδ : 0 < δ) (S : Finset ℕ) (H : ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hsmall : ∀ p ∈ S, ∀ q ∈ S, |Real.log q - Real.log p - c| ≤ D / 2)
    (havoid : ∀ p ∈ S, ∀ q ∈ S, δ ≤ |Real.log q - Real.log p - c|) :
    pairEnergy S (primeWeight ε) (fun p => Real.log p) c D H ≤
      D ^ 2 * rowConstant δ * (∑ p ∈ S, primeWeight ε p) := by
  have hrow (p : ℕ) (hp : p ∈ S) :
      (∑ q ∈ S, primeWeight ε q *
        ‖dirichletKernel H ((Real.log q - Real.log p - c) / D)‖ ^ 2) ≤ D ^ 2 * rowConstant δ := by
    calc
      _ ≤ ∑ q ∈ S, primeWeight ε q *
          (D ^ 2 * ((1 + 1 / δ ^ 2) / (1 + (Real.log q - Real.log p - c) ^ 2))) := by
        apply sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left
          (kernel_sq_le_lorentz H hD hδ (havoid p hp q hq) (hsmall p hp q hq))
          (primeWeight_nonneg ε (hS q hq))
      _ = (D ^ 2 * (1 + 1 / δ ^ 2)) *
          ∑ q ∈ S, primeWeight ε q / (1 + (Real.log q - (Real.log p + c)) ^ 2) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro q hq
        ring
      _ ≤ (D ^ 2 * (1 + 1 / δ ^ 2)) * (3 * (Real.exp 1 * Real.log 4) * lorentzMass) :=
        mul_le_mul_of_nonneg_left (sum_primeWeight_lorentz_le hε S (Real.log p + c) hS)
          (by positivity)
      _ = D ^ 2 * rowConstant δ := by unfold rowConstant; ring
  unfold pairEnergy
  rw [sum_product]
  calc
    _ = ∑ p ∈ S, primeWeight ε p * (∑ q ∈ S, primeWeight ε q *
        ‖dirichletKernel H ((Real.log q - Real.log p - c) / D)‖ ^ 2) := by
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      apply sum_congr rfl
      intro q hq
      ring
    _ ≤ ∑ p ∈ S, primeWeight ε p * (D ^ 2 * rowConstant δ) := by
      exact sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hrow p hp)
        (primeWeight_nonneg ε (hS p hp)))
    _ = _ := by rw [← sum_mul]; ring

#print axioms pairEnergy_upper_of_avoids
#print axioms pairEnergy_fourier
#print axioms matrix_band_lower

end Erdos972PrimeRatioKernel
