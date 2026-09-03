import Submission.UniformDampedTail

/-! The fixed-parameter full correlation admits a finite-divisor
approximation uniformly in the outer cutoff N. No uniformity as t tends
to zero is asserted. -/
namespace Erdos972UniformSmoothCorrelationTail

open Finset Filter
open Erdos972PrimePowerError Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972SmoothDivisorTail Erdos972UniformDampedTail

lemma pair_perturbation_energy {f g p q η : ℝ}
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hη : 0 < η) :
    |f*g-p*q| ≤ 2*η + (1/η+1)*((f-p)^2+(g-q)^2) := by
  have h := pair_perturbation_bound (p := p) (q := q) hf0 hf1 hg0 hg1 (by norm_num : (0 : ℝ) ≤ 1)
    (abs_nonneg (f-p)) (abs_nonneg (g-q)) (by simp) (by simp)
  simp only [one_mul, one_pow, sq_abs] at h
  have hr : |f-p| ≤ η+(f-p)^2/η := by
    have hh : (|f-p|-η)*η ≤ (f-p)^2 := by
      nlinarith only [sq_nonneg (|f-p|-η), sq_abs (f-p), sq_nonneg η]
    have := (le_div_iff₀ hη).mpr hh
    linarith
  have hs : |g-q| ≤ η+(g-q)^2/η := by
    have hh : (|g-q|-η)*η ≤ (g-q)^2 := by
      nlinarith only [sq_nonneg (|g-q|-η), sq_abs (g-q), sq_nonneg η]
    have := (le_div_iff₀ hη).mpr hh
    linarith
  have hsq : 0 ≤ (f-p)^2+(g-q)^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have he : (1/η+1)*((f-p)^2+(g-q)^2) =
      (f-p)^2/η+(g-q)^2/η+(f-p)^2+(g-q)^2 := by ring
  rw [he]
  linarith

lemma output_tail_energy {α t δ : ℝ} (hα : 1 ≤ α) (hδ : 0 ≤ δ) (D N : ℕ)
    (hbound : ∀ M : ℕ, (∑ n ∈ Ioc 0 M, (expTail t D n)^2) ≤ δ*M) :
    (∑ n ∈ Ioc 0 N, (expTail t D (floorMul α n))^2) ≤ δ*α*N := by
  classical
  calc
    _ = ∑ m ∈ (Ioc 0 N).image (floorMul α), (expTail t D m)^2 := by
      rw [sum_image]
      exact (floorMul_strictMono hα).injective.injOn
    _ ≤ ∑ m ∈ Ioc 0 (floorMul α N), (expTail t D m)^2 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro m hm
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
        exact mem_Ioc.mpr ⟨floorMul_pos hα (mem_Ioc.mp hn).1,
          (floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2⟩
      · intro m _ _
        exact sq_nonneg _
    _ ≤ δ*floorMul α N := hbound _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (floorMul_le_real hα (le_refl N)) hδ
      simpa only [mul_assoc] using hh

lemma correlation_error_of_uniform_energy {α t δ η : ℝ}
    (hα : 1 ≤ α) (ht : 0 ≤ t) (hδ : 0 ≤ δ) (hη : 0 < η) (D N : ℕ)
    (hbound : ∀ M : ℕ, (∑ n ∈ Ioc 0 M, (expTail t D n)^2) ≤ δ*M) :
    |fullExpCorrelation t α N-truncatedExpCorrelation t α D N| ≤
      (2*η+(1/η+1)*δ*(1+α))*N := by
  have hp (n : ℕ) :
      |expDivisorSum t n*expDivisorSum t (floorMul α n)-
        truncatedExpSum t D n*truncatedExpSum t D (floorMul α n)| ≤
        2*η+(1/η+1)*((expTail t D n)^2+(expTail t D (floorMul α n))^2) :=
    pair_perturbation_energy (expDivisorSum_nonneg ht _) (expDivisorSum_le_one ht _)
      (expDivisorSum_nonneg ht _) (expDivisorSum_le_one ht _) hη
  unfold fullExpCorrelation truncatedExpCorrelation
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Ioc 0 N,
        (2*η+(1/η+1)*((expTail t D n)^2+(expTail t D (floorMul α n))^2)) :=
      sum_le_sum (fun n _ => hp n)
    _ = (N : ℝ)*(2*η) + (1/η+1)*
        ((∑ n ∈ Ioc 0 N, (expTail t D n)^2)+
          ∑ n ∈ Ioc 0 N, (expTail t D (floorMul α n))^2) := by
      simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
      ring
    _ ≤ (N : ℝ)*(2*η)+(1/η+1)*(δ*N+δ*α*N) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left
        (add_le_add (hbound N) (output_tail_energy hα hδ D N hbound)) (show 0 ≤ 1/η+1 by positivity)) _
    _ = _ := by ring

/-- For fixed t>0 and slope alpha>=1, one finite divisor cutoff works for
all N. This quantifier order is stronger than choosing D separately for
each N, but still does not give a simultaneous limit with t tending to zero. -/
theorem exists_uniform_correlation_cutoff {α t ε : ℝ}
    (hα : 1 ≤ α) (ht : 0 < t) (hε : 0 < ε) :
    ∃ D : ℕ, ∀ N : ℕ,
      |fullExpCorrelation t α N-truncatedExpCorrelation t α D N| ≤ ε*N := by
  let η := ε/4
  let δ := ε/(2*(1/η+1)*(1+α))
  have hη : 0 < η := by dsimp [η]; positivity
  have hc : 0 < 1/η+1 := by positivity
  have hαc : 0 < 1+α := by linarith
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨D, hD⟩ := exists_uniform_tail_cutoff ht hδ
  refine ⟨D, fun N => ?_⟩
  have hh := correlation_error_of_uniform_energy hα ht.le hδ.le hη D N hD
  have he : 2*η+(1/η+1)*δ*(1+α) = ε := by
    dsimp only [δ]
    field_simp
    dsimp only [η]
    ring
  rwa [he] at hh

#print axioms correlation_error_of_uniform_energy
#print axioms exists_uniform_correlation_cutoff

end Erdos972UniformSmoothCorrelationTail
