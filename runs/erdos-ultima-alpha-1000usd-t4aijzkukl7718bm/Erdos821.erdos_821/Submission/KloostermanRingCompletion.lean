import Submission.SquarefreeKloosterman

/-!
# Completion over finite commutative rings

Nonzero frequencies are summed over `univ.erase 0`, not over the unit group.
This distinction retains the frequencies needed at composite moduli.
-/
open Finset
open scoped Classical BigOperators
namespace Erdos821.Kloosterman

section FiniteRing
variable {R : Type*} [CommRing R] [Fintype R]

noncomputable def ringFourier (ψ : AddChar R ℂ) (w : R → ℂ) (t : R) : ℂ :=
  ∑ x : R, w x * ψ (-t*x)

noncomputable def ringFourierMass (ψ : AddChar R ℂ) (w : R → ℂ) : ℝ :=
  ∑ t : R, ‖ringFourier ψ w t‖

lemma ringFourier_inversion (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (w : R → ℂ) (x : R) :
    (∑ t : R, ringFourier ψ w t * ψ (t*x)) = (Fintype.card R : ℂ)*w x := by
  have hkernel (y : R) : (∑ t : R, ψ (t*(x-y))) =
      if y=x then (Fintype.card R : ℂ) else 0 := by
    rw [AddChar.sum_mulShift _ hψ]
    by_cases h : y=x
    · simp [h]
    · simp [sub_ne_zero.mpr (Ne.symm h), h]
  calc
    _ = ∑ t : R, ∑ y : R, w y*ψ (t*(x-y)) := by
      simp only [ringFourier, sum_mul]
      apply sum_congr rfl
      intro t _
      apply sum_congr rfl
      intro y _
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = ∑ y : R, w y * ∑ t : R, ψ (t*(x-y)) := by
      rw [sum_comm]
      simp only [mul_sum]
    _ = _ := by simp [hkernel, mul_ite, mul_comm]

noncomputable def ringWeightedKloosterman (ψ : AddChar R ℂ) (w : R → ℂ) (a b : R) : ℂ :=
  ∑ u : Rˣ, w u * ψ (a*(u : R)+b*(↑(u⁻¹) : R))

lemma ringWeightedKloosterman_completion (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (w : R → ℂ) (a b : R) :
    (Fintype.card R : ℂ)*ringWeightedKloosterman ψ w a b =
      ∑ t : R, ringFourier ψ w t * ringKloosterman ψ (a+t) b := by
  calc
    _ = ∑ u : Rˣ, (∑ t : R, ringFourier ψ w t * ψ (t*(u : R))) *
        ψ (a*(u : R)+b*(↑(u⁻¹) : R)) := by
      simp only [ringFourier_inversion ψ hψ, ringWeightedKloosterman, mul_sum, mul_assoc]
    _ = ∑ u : Rˣ, ∑ t : R,
        ringFourier ψ w t * ψ ((a+t)*(u : R)+b*(↑(u⁻¹) : R)) := by
      simp only [sum_mul]
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro t _
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = _ := by rw [sum_comm]; simp only [ringKloosterman, mul_sum]

lemma ringWeightedKloosterman_norm_le_of_bound (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (w : R → ℂ) (a b : R) (B : ℝ)
    (hB : ∀ t : R, ‖ringKloosterman ψ (a+t) b‖ ≤ B) :
    (Fintype.card R : ℝ)*‖ringWeightedKloosterman ψ w a b‖ ≤ B*ringFourierMass ψ w := by
  calc
    _ = ‖(Fintype.card R : ℂ)*ringWeightedKloosterman ψ w a b‖ := by
      rw [norm_mul, Complex.norm_natCast]
    _ = ‖∑ t : R, ringFourier ψ w t * ringKloosterman ψ (a+t) b‖ := by
      rw [ringWeightedKloosterman_completion ψ hψ]
    _ ≤ ∑ t : R, ‖ringFourier ψ w t * ringKloosterman ψ (a+t) b‖ := norm_sum_le _ _
    _ ≤ ∑ t : R, ‖ringFourier ψ w t‖ * B := by
      apply sum_le_sum
      intro t _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB t) (norm_nonneg _)
    _ = _ := by rw [← sum_mul, ringFourierMass, mul_comm]

noncomputable def ringUnitMass (w : R → ℂ) : ℂ := ∑ u : Rˣ, w u

noncomputable def ringHyperbolaWeight (w z : R → ℂ) (r : R) : ℂ :=
  ∑ u : Rˣ, w u * z (r*(↑(u⁻¹) : R))

lemma ringFourier_zero (ψ : AddChar R ℂ) (w : R → ℂ) :
    ringFourier ψ w 0 = ∑ x : R, w x := by
  simp [ringFourier]

lemma ringWeightedKloosterman_zero (ψ : AddChar R ℂ) (w : R → ℂ) :
    ringWeightedKloosterman ψ w 0 0 = ringUnitMass w := by
  simp [ringWeightedKloosterman, ringUnitMass]

lemma ringHyperbolaWeight_completion (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (w z : R → ℂ) (r : R) :
    (Fintype.card R : ℂ)*ringHyperbolaWeight w z r =
      ∑ t : R, ringFourier ψ z t * ringWeightedKloosterman ψ w 0 (t*r) := by
  calc
    _ = ∑ u : Rˣ, w u * (∑ t : R, ringFourier ψ z t * ψ (t*(r*(↑(u⁻¹) : R)))) := by
      simp only [ringFourier_inversion ψ hψ, ringHyperbolaWeight, mul_sum]
      apply sum_congr rfl
      intro u _
      ring
    _ = ∑ u : Rˣ, ∑ t : R, ringFourier ψ z t *
        (w u * ψ ((t*r)*(↑(u⁻¹) : R))) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro t _
      rw [← mul_assoc t r (↑(u⁻¹) : R)]
      ring
    _ = _ := by
      rw [sum_comm]
      simp only [ringWeightedKloosterman, zero_mul, zero_add, mul_sum]

lemma ringHyperbolaWeight_error_identity (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (w z : R → ℂ) (r : R) :
    (Fintype.card R : ℂ)*ringHyperbolaWeight w z r - (∑ x : R, z x)*ringUnitMass w =
      ∑ t ∈ (univ : Finset R).erase 0, ringFourier ψ z t * ringWeightedKloosterman ψ w 0 (t*r) := by
  have hh := sum_erase_add univ (fun t : R =>
    ringFourier ψ z t * ringWeightedKloosterman ψ w 0 (t*r)) (mem_univ 0)
  dsimp only at hh
  rw [← ringHyperbolaWeight_completion ψ hψ w z r, zero_mul,
    ringFourier_zero, ringWeightedKloosterman_zero] at hh
  exact (eq_sub_of_add_eq hh).symm

lemma ringHyperbolaWeight_error_norm_le (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (w z : R → ℂ) (r : R) (B : R → ℝ)
    (hB : ∀ t ∈ (univ : Finset R).erase 0, ‖ringWeightedKloosterman ψ w 0 (t*r)‖ ≤ B t) :
    ‖(Fintype.card R : ℂ)*ringHyperbolaWeight w z r - (∑ x : R, z x)*ringUnitMass w‖ ≤
      ∑ t ∈ (univ : Finset R).erase 0, B t * ‖ringFourier ψ z t‖ := by
  rw [ringHyperbolaWeight_error_identity ψ hψ]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro t ht
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (hB t ht) (norm_nonneg _)).trans_eq (mul_comm _ _)

end FiniteRing

noncomputable def squarefreeBound (q : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt ((3 : ℝ)^q.primeFactors.card*(q : ℝ)^3))

lemma squarefreeBound_nonneg (q : ℕ) : 0 ≤ squarefreeBound q := Real.sqrt_nonneg _

lemma squarefreeBound_fourth (q : ℕ) :
    squarefreeBound q ^ 4 = (3 : ℝ)^q.primeFactors.card*(q : ℝ)^3 := by
  rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, squarefreeBound,
    Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]

/-- A deliberately coarser gcd loss is convenient for summing interval frequencies. -/
lemma ringKloosterman_squarefree_norm (q : ℕ) [NeZero q] (hq : Squarefree q)
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (a b : ZMod q) :
    ‖ringKloosterman ψ a b‖ ≤ squarefreeBound q * (Nat.gcd b.val q : ℕ) := by
  have hg : (1 : ℝ) ≤ (Nat.gcd b.val q : ℕ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.gcd_ne_zero_right (NeZero.ne q))
  apply (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (squarefreeBound_nonneg q) (Nat.cast_nonneg _)) (by decide : 4 ≠ 0)).mp
  rw [mul_pow, squarefreeBound_fourth]
  apply (ringKloosterman_squarefree_fourth q hq ψ hψ a b).trans
  exact mul_le_mul_of_nonneg_left (le_self_pow₀ hg (by decide : 4 ≠ 0)) (by positivity)

end Erdos821.Kloosterman
