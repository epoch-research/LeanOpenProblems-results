import Submission.EulerMassQuantitativeSectors
import Submission.BuchstabSectorSums

/-! A mesh-independent quadrature estimate for monotone prime profiles.
Summation by parts charges the variation of the profile, not the number of
prime sectors. This is an auxiliary finite-prime estimate, not a settlement
of the quadratic Jacobsthal conjecture. -/
namespace Erdos970.FiniteSelberg
open Finset Real
set_option maxHeartbeats 1400000

lemma weighted_increments_by_parts (b e : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ range N, b i*(e (i+1)-e i)) =
      b N*e N-b 0*e 0+∑ i ∈ range N, (b i-b (i+1))*e (i+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ,sum_range_succ,ih]
      ring

/-- Bounded error in the cumulative weights gives a total error controlled by
just the endpoint of a nonnegative antitone profile, independently of N. -/
theorem antitone_weighted_increments_abs_le (b e : ℕ → ℝ) (N : ℕ) (E : ℝ)
    (hE : 0 ≤ E) (hb : ∀ i, 0 ≤ b i) (hanti : Antitone b)
    (he : ∀ i, i ≤ N → |e i| ≤ E) :
    |∑ i ∈ range N, b i*(e (i+1)-e i)| ≤ 2*b 0*E := by
  have hterm (i : ℕ) (hi : i ∈ range N) :
      |(b i-b (i+1))*e (i+1)| ≤ (b i-b (i+1))*E := by
    have hnon : 0 ≤ b i-b (i+1) := sub_nonneg.mpr (hanti (Nat.le_succ i))
    rw [abs_mul,abs_of_nonneg hnon]
    exact mul_le_mul_of_nonneg_left (he (i+1) (by have := mem_range.mp hi; omega)) hnon
  have hsum : |∑ i ∈ range N, (b i-b (i+1))*e (i+1)| ≤ (b 0-b N)*E := by
    apply (abs_sum_le_sum_abs _ _).trans
    have hh := sum_le_sum hterm
    rwa [← sum_mul,sum_range_sub'] at hh
  have hend (i : ℕ) (hi : i ≤ N) : |b i*e i| ≤ b i*E := by
    rw [abs_mul,abs_of_nonneg (hb i)]
    exact mul_le_mul_of_nonneg_left (he i hi) (hb i)
  rw [weighted_increments_by_parts]
  calc
    _ ≤ |b N*e N-b 0*e 0|+|∑ i ∈ range N, (b i-b (i+1))*e (i+1)| :=
      abs_add_le _ _
    _ ≤ (|b N*e N|+|b 0*e 0|)+(b 0-b N)*E :=
      add_le_add (abs_sub _ _) hsum
    _ ≤ (b N*E+b 0*E)+(b 0-b N)*E :=
      add_le_add (add_le_add (hend N le_rfl) (hend 0 (Nat.zero_le N))) le_rfl
    _ = _ := by ring

/-- Uniform cumulative-weight error on every scale at least a. -/
theorem scaledEulerMass_ratio_uniform_remainder (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A)
    (a v t L : ℝ) (ha : 0 < a) (hv : 0 ≤ v) (hat : a ≤ t) (hL : 0 < L)
    (hvL : 2 ≤ v*L) (haL : 2 ≤ a*L) (hlarge : 2*(A+C) ≤ C*(a*L)) :
    |initialEulerMass (expFloor v L)/initialEulerMass (expFloor t L)-v/t| ≤
      (2*(A+C)/(C*(a*L)))*(1+v/a) := by
  have ht : 0 < t := ha.trans_le hat
  have hscale := mul_le_mul_of_nonneg_right hat hL.le
  have hh := scaledEulerMass_ratio_remainder C A hC hA hrem v t L hv ht hL hvL
    (haL.trans hscale) (hlarge.trans (mul_le_mul_of_nonneg_left hscale hC.le))
  apply hh.trans
  apply mul_le_mul
  · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hscale hC.le)
  · exact add_le_add le_rfl (div_le_div_of_nonneg_left hv ha hat)
  · positivity
  · positivity

/-- Whole-profile quadrature, not the sum of separate absolute sector errors.
The error has no factor N, even though all endpoints and coefficients may
vary with the level. Prime sectors are in decreasing scale order, so the
profile coefficients may be antitone in the increasing child-level order. -/
theorem firstHit_monotone_profile_remainder (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A)
    (a v L : ℝ) (ha : 0 < a) (hv : 0 ≤ v) (hL : 0 < L)
    (hvL : 2 ≤ v*L) (haL : 2 ≤ a*L) (hlarge : 2*(A+C) ≤ C*(a*L))
    (N : ℕ) (t b : ℕ → ℝ) (ht : ∀ i, i ≤ N → a ≤ t i)
    (htanti : ∀ i, i < N → t (i+1) ≤ t i)
    (hb : ∀ i, 0 ≤ b i) (hbanti : Antitone b) :
    |(∑ i ∈ range N, b i*firstHitSectorMass v (t (i+1)) (t i) L)-
      (∑ i ∈ range N, b i*(v/t (i+1)-v/t i))| ≤
        (4*(A+C)/(C*(a*L)))*(1+v/a)*b 0 := by
  let e : ℕ → ℝ := fun i =>
    initialEulerMass (expFloor v L)/initialEulerMass (expFloor (t i) L)-v/t i
  let E : ℝ := (2*(A+C)/(C*(a*L)))*(1+v/a)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have he : ∀ i, i ≤ N → |e i| ≤ E := by
    intro i hi
    exact scaledEulerMass_ratio_uniform_remainder C A hC hA hrem a v (t i) L
      ha hv (ht i hi) hL hvL haL hlarge
  have hid (i : ℕ) (hi : i ∈ range N) :
      firstHitSectorMass v (t (i+1)) (t i) L-(v/t (i+1)-v/t i) = e (i+1)-e i := by
    have hiN := mem_range.mp hi
    have horder : expFloor (t (i+1)) L ≤ expFloor (t i) L :=
      Nat.floor_le_floor (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (htanti i hiN) hL.le))
    rw [firstHitSectorMass,density_annulus_telescope _ _ horder]
    dsimp only [e]
    ring
  have hsum : (∑ i ∈ range N, b i*firstHitSectorMass v (t (i+1)) (t i) L)-
      (∑ i ∈ range N, b i*(v/t (i+1)-v/t i)) =
      ∑ i ∈ range N, b i*(e (i+1)-e i) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    rw [← mul_sub,hid i hi]
  rw [hsum]
  have hh := antitone_weighted_increments_abs_le b e N E hE hb hbanti he
  convert hh using 1 <;> dsimp [E] <;> ring

/-- Direct majorant for actual prime sums, keeping the mesh-independent
remainder and the continuous rectangle main term separately. -/
theorem firstHit_monotone_profile_majorant (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A)
    (a v L : ℝ) (ha : 0 < a) (hv : 0 ≤ v) (hL : 0 < L)
    (hvL : 2 ≤ v*L) (haL : 2 ≤ a*L) (hlarge : 2*(A+C) ≤ C*(a*L))
    (N : ℕ) (t b : ℕ → ℝ) (ht : ∀ i, i ≤ N → a ≤ t i)
    (htanti : ∀ i, i < N → t (i+1) ≤ t i)
    (hb : ∀ i, 0 ≤ b i) (hbanti : Antitone b) (F : ℕ → ℝ)
    (hF : ∀ i ∈ range N, ∀ p ∈
      (Ioc (expFloor (t (i+1)) L) (expFloor (t i) L)).filter Nat.Prime,
      F p ≤ b i*((1/(p : ℝ))*(1/eulerMass p.primesBelow))) :
    initialEulerMass (expFloor v L)*
      (∑ i ∈ range N, ∑ p ∈
        (Ioc (expFloor (t (i+1)) L) (expFloor (t i) L)).filter Nat.Prime, F p) ≤
      (∑ i ∈ range N, b i*(v/t (i+1)-v/t i))+
        (4*(A+C)/(C*(a*L)))*(1+v/a)*b 0 := by
  have hcomp : initialEulerMass (expFloor v L)*
      (∑ i ∈ range N, ∑ p ∈
        (Ioc (expFloor (t (i+1)) L) (expFloor (t i) L)).filter Nat.Prime, F p) ≤
      ∑ i ∈ range N, b i*firstHitSectorMass v (t (i+1)) (t i) L := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have hh := sum_le_sum (fun p hp => hF i hi p hp)
    rw [← mul_sum] at hh
    have hm := mul_le_mul_of_nonneg_left hh (initialEulerMass_pos (expFloor v L)).le
    simpa only [firstHitSectorMass,mul_assoc,mul_comm,mul_left_comm] using hm
  have he := (abs_le.mp (firstHit_monotone_profile_remainder C A hC hA hrem a v L
    ha hv hL hvL haL hlarge N t b ht htanti hb hbanti)).2
  linarith only [hcomp,he]

#print axioms antitone_weighted_increments_abs_le
#print axioms scaledEulerMass_ratio_uniform_remainder
#print axioms firstHit_monotone_profile_remainder
#print axioms firstHit_monotone_profile_majorant
end Erdos970.FiniteSelberg
