import FormalConjecturesUtil

/-! Finite occupancy calculations for an auxiliary column-splitting construction.
No assertion about extremal-number exponents is made here. -/
open Finset
open scoped BigOperators Classical
namespace Erdos713FiniteOccupancy
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Nonempty J]
set_option maxHeartbeats 1000000

lemma expect_eval (i : I) (g : J → ℝ) :
    (𝔼 (f : I → J), g (f i)) = 𝔼 y : J, g y := by
  classical
  let e := Equiv.funSplitAt i J
  calc
    _ = 𝔼 (p : J × ({j : I // j ≠ i} → J)), g p.1 :=
      Fintype.expect_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      rw [← univ_product_univ, expect_product]
      simp only [Fintype.expect_const]

lemma expect_eval_mul {i j : I} (hij : i ≠ j) (g h : J → ℝ) :
    (𝔼 (f : I → J), g (f i) * h (f j)) =
      (𝔼 y : J, g y) * (𝔼 y : J, h y) := by
  classical
  let e := Equiv.funSplitAt i J
  calc
    _ = 𝔼 (p : J × ({j : I // j ≠ i} → J)), g p.1 * h (p.2 ⟨j,hij.symm⟩) :=
      Fintype.expect_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      rw [← univ_product_univ, expect_product]
      simp_rw [← mul_expect]
      rw [expect_eval (I := {j : I // j ≠ i}) ⟨j,hij.symm⟩ h]
      rw [← expect_mul]

/-- The variance identity is a finite sum, not a measure-theoretic assumption. -/
lemma indicator_variance (S : Finset I) (g : J → ℝ)
    (hg : ∀ y, (g y)^2 = g y) (p : ℝ) (hp : (𝔼 y : J, g y) = p) :
    (𝔼 (f : I → J), (∑ i ∈ S, g (f i) - S.card*p)^2) =
      S.card*p*(1-p) := by
  classical
  have hz : (𝔼 y : J, (g y-p)) = 0 := by
    rw [expect_sub_distrib, hp, Fintype.expect_const, sub_self]
  have hd : (𝔼 y : J, (g y-p)^2) = p*(1-p) := by
    have he (y : J) : (g y-p)^2 = g y-2*p*g y+p^2 := by nlinarith [hg y]
    simp_rw [he]
    rw [expect_add_distrib, expect_sub_distrib, ← mul_expect, hp, Fintype.expect_const]
    ring
  have he (f : I → J) : (∑ i ∈ S, g (f i) - S.card*p)^2 =
      ∑ i ∈ S, ∑ j ∈ S, (g (f i)-p)*(g (f j)-p) := by
    rw [← sum_mul_sum, sum_sub_distrib]
    simp only [sum_const, nsmul_eq_mul, pow_two]
  simp_rw [he, expect_sum_comm]
  calc
    _ = ∑ _i ∈ S, p*(1-p) := by
      apply sum_congr rfl
      intro i hi
      rw [sum_eq_single i]
      · simp only [← pow_two]
        exact (expect_eval i (fun y => (g y-p)^2)).trans hd
      · intro j _hj hji
        rw [expect_eval_mul hji.symm (fun y => g y-p) (fun y => g y-p), hz, zero_mul]
      · exact fun hn => (hn hi).elim
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

/-- A finite second-moment bound suffices for a uniform lower bound on heaviness. -/
lemma heavy_of_variance {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (L : ℝ) (hL : 8 ≤ L)
    (hv : (𝔼 ω, (X ω-L)^2) ≤ L) :
    (1/2 : ℝ) ≤ 𝔼 ω, (if 3 ≤ X ω then (1 : ℝ) else 0) := by
  classical
  have hpoint (ω : Ω) : L^2 ≤
      L^2*(if 3 ≤ X ω then (1 : ℝ) else 0)+4*(X ω-L)^2 := by
    split_ifs with h
    · nlinarith [sq_nonneg (X ω-L)]
    · have hx : X ω < 3 := lt_of_not_ge h
      have hsq := mul_self_le_mul_self (by linarith : 0 ≤ L/2)
        (by linarith : L/2 ≤ L-X ω)
      nlinarith only [hsq]
  have havg := expect_le_expect (s := univ) (fun ω _ => hpoint ω)
  rw [Fintype.expect_const, expect_add_distrib, ← mul_expect, ← mul_expect] at havg
  by_contra hn
  have hl : (𝔼 ω, if 3 ≤ X ω then (1 : ℝ) else 0) < 1/2 := lt_of_not_ge hn
  have hpos : 0 < L^2 := sq_pos_of_pos (by linarith)
  have hlt := mul_lt_mul_of_pos_left hl hpos
  nlinarith [mul_nonneg (by linarith : 0 ≤ L) (by linarith : 0 ≤ L-8)]

#print axioms expect_eval
#print axioms expect_eval_mul
#print axioms indicator_variance
#print axioms heavy_of_variance
end Erdos713FiniteOccupancy
