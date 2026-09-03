import Submission.PrefixPrimeRotation
import Submission.WeightedIntervalDiscrepancy

/-! Quantitative weighted interval discrepancy at simultaneous good rational
scales. This counts one Mangoldt variable in a rotation arc. -/
namespace Erdos972WeightedPrimeRotation

open Finset Complex ArithmeticFunction
open scoped ComplexConjugate
open Erdos972ExponentialSum Erdos972VaughanSums Erdos972PrimeRotation
open Erdos972PrimeFejer Erdos972PrefixPrimeRotation Erdos972DiscreteFejer
open Erdos972WeightedIntervalDiscrepancy

lemma expSum_neg (θ : ℝ) (N : ℕ) : expSum vonMangoldt (-θ) N = conj (expSum vonMangoldt θ N) := by
  unfold expSum
  simp only [map_sum, map_mul, Complex.conj_ofReal, conjugate_phase, neg_mul]

lemma norm_expSum_difference_le (θ E : ℝ) (N H : ℕ)
    (hE : ∀ h : ℕ, 0 < h → h ≤ H → ‖expSum vonMangoldt ((h : ℝ)*θ) N‖ ≤ E)
    {i j : ℕ} (hi : i < H) (hj : j < H) (hij : i ≠ j) :
    ‖expSum vonMangoldt (((i : ℝ)-j)*θ) N‖ ≤ E := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · have he : ((i : ℝ)-j)*θ = -((j-i : ℕ)*θ) := by rw [Nat.cast_sub hij.le]; ring
    rw [he, expSum_neg, norm_conj]
    exact hE (j-i) (Nat.sub_pos_of_lt hij) ((Nat.sub_le j i).trans hj.le)
  · have he : ((i : ℝ)-j)*θ = (i-j : ℕ)*θ := by rw [Nat.cast_sub hji.le]
    rw [he]
    exact hE (i-j) (Nat.sub_pos_of_lt hji) ((Nat.sub_le i j).trans hi.le)

lemma weightedFourier_rotation (θ t h : ℝ) (N : ℕ) :
    weightedFourier (Ioc 0 N) (fun n => vonMangoldt n) (fun n => θ*n+t) h =
      phase (h*t) * expSum vonMangoldt (h*θ) N := by
  unfold weightedFourier expSum
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [show h*(θ*n+t) = h*t+(h*θ)*n by ring, phase_add]
  ring

noncomputable def mangoldtArcSum (θ t a b : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ (Ioc 0 N).filter (fun n : ℕ => a ≤ Int.fract (θ*n+t) ∧ Int.fract (θ*n+t) < b), vonMangoldt n

/-- A quantitative weighted Weyl estimate, uniform in the translation of the
rotation points. -/
theorem mangoldt_arc_discrepancy (θ t : ℝ) (N : ℕ)
    {H : ℕ} [NeZero H] (a b δ E : ℝ) (hab : a ≤ b) (hδ : 0 < δ)
    (hδa : δ ≤ a) (hδb : δ ≤ 1-b) (hE0 : 0 ≤ E)
    (hE : ∀ h : ℕ, 0 < h → h ≤ H → ‖expSum vonMangoldt ((h : ℝ)*θ) N‖ ≤ E) :
    |mangoldtArcSum θ t a b N - (b-a)*Chebyshev.psi N| ≤
      (2*δ + 1/(H : ℝ) + 4/((4*δ)^2 * H))*Chebyshev.psi N + H*E := by
  have hh := weighted_interval_discrepancy (Ioc 0 N) (fun n => vonMangoldt n) (fun n => θ*n+t)
    (fun _ _ => vonMangoldt_nonneg) a b δ E hab hδ hδa hδb hE0
    (fun i j hi hj hij => by
      rw [weightedFourier_rotation, norm_mul, norm_phase, one_mul]
      exact norm_expSum_difference_le θ E N H hE hi hj hij)
  simpa only [mangoldtArcSum, Chebyshev.psi, Nat.floor_natCast] using hh

/-- Uniform-prefix interval discrepancy follows from one base approximation;
`H` is allowed to vary with the rational scale. -/
theorem simultaneous_arc_prefix_discrepancy {θ : ℝ} (hθ : 1 < θ)
    (r : ℚ) (hr : |θ-r| ≤ 1/(r.den : ℝ)^2)
    (u H : ℕ) (hH : 0 < H) (hu : 512*H ≤ u)
    (hlo : u^4 ≤ r.den) (hhi : r.den ≤ 16*u^4)
    (a b δ t : ℝ) (hab : a ≤ b) (hδ : 0 < δ) (hδa : δ ≤ a) (hδb : δ ≤ 1-b)
    (X : ℕ) (hX : X ≤ u^6) :
    |mangoldtArcSum θ t a b X - (b-a)*Chebyshev.psi X| ≤
      (2*δ + 1/(H : ℝ) + 4/((4*δ)^2 * H))*Chebyshev.psi X +
      H * (rotationConstant (64*H) * (1+Real.log u)^5 * (u : ℝ)^5 * Real.sqrt u) := by
  letI : NeZero H := ⟨Nat.ne_of_gt hH⟩
  exact mangoldt_arc_discrepancy θ t X a b δ _ hab hδ hδa hδb
    (by positivity [rotationConstant_pos (64*H), Real.log_natCast_nonneg u])
    (fun h hh hhH => simultaneous_prefix_bound hθ r hr u H hH hu hlo hhi h hh hhH X hX)

lemma rotationConstant_mul_le (K H : ℕ) (hH : 0 < H) :
    rotationConstant (K*H) ≤ rotationConstant K * (H : ℝ)^2 := by
  have hh : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hh2 : (H : ℝ) ≤ (H : ℝ)^2 := by nlinarith
  have he := Real.exp_pos (2*Real.pi)
  unfold rotationConstant
  push_cast
  nlinarith [mul_nonneg (show 0 ≤ (H : ℝ)^2 - H by linarith)
    (show 0 ≤ 192*(K : ℝ) + 130000*Real.exp (2*Real.pi)*K by positivity),
    mul_nonneg (show 0 ≤ (H : ℝ)^2 - 1 by nlinarith)
    (show 0 ≤ 7 + 520000*Real.exp (2*Real.pi) by positivity)]

#print axioms mangoldt_arc_discrepancy
#print axioms simultaneous_arc_prefix_discrepancy
#print axioms rotationConstant_mul_le

end Erdos972WeightedPrimeRotation
