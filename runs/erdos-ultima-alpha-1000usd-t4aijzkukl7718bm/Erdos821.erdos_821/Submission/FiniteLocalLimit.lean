import Submission.FiniteLocalDensity
import Submission.UnitSlopeMultiplicity

/-!
# A limiting multiplicity exponent from all finite local corrections

The local prime cutoff and every geometric parameter are fixed before the
scale tends to infinity. The limit 2303/4351 is still strictly below one.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma finite_local_parametric_budget (D N M k : ℕ) (hD : 2 ≤ D) (hM : 1 ≤ M)
    (hC : (2048/255 : ℝ)*Sieve.localAverageConstant D=(N : ℝ)/(M : ℝ)) :
    finiteBlockMainLimit D (widePairScale ((2*N+M)*k)) (4*N*k+16) (2*M*k) < 1 := by
  apply (finiteBlockMainLimit_le_telescoped _ _ _ _ hD (by omega)).trans_lt
  rw [hC]
  have hden : (0 : ℝ) < (((4*N*k+16 : ℕ) : ℝ)-2)*
      ((((4*N*k+16 : ℕ) : ℝ)+(2*M*k : ℕ))-2) := by
    push_cast
    have hNk : (0 : ℝ) ≤ (N : ℝ)*k := by positivity
    have hMk : (0 : ℝ) ≤ (M : ℝ)*k := by positivity
    exact mul_pos (by linarith) (by linarith)
  apply (div_lt_one hden).mpr
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have he : (((4*N*k+16 : ℕ) : ℝ)-2)*((((4*N*k+16 : ℕ) : ℝ)+(2*M*k : ℕ))-2) -
      (N : ℝ)/(M : ℝ)*(widePairScale ((2*N+M)*k) : ℝ)*(2*M*k : ℕ) =
        (72*(N : ℝ)+28*(M : ℝ))*k+196 := by
    simp only [widePairScale,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    field_simp
    ring
  have hpos : (0 : ℝ) < (72*(N : ℝ)+28*(M : ℝ))*k+196 := by positivity
  linarith only [he,hpos]

lemma exists_finite_local_parametric_count (D N M k : ℕ)
    (hD : 2 ≤ D) (hN : 22 ≤ N) (hM : 1 ≤ M) (hMN : M ≤ N) (hk : 1 ≤ k)
    (hC : (2048/255 : ℝ)*Sieve.localAverageConstant D=(N : ℝ)/(M : ℝ)) :
    ∃ C : ℕ, 0<C ∧ ∀ᶠ m : ℕ in atTop,
      (independentN (4*(2*N+M)*k+20) m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN (4*(2*N+M)*k+20) m)
          (independentN (4*N*k+21) m)).card : ℝ) := by
  have hNk : N ≤ N*k := Nat.le_mul_of_pos_right N hk
  have hMk : M*k ≤ N*k := Nat.mul_le_mul_right k hMN
  have hMkp : 0<M*k := Nat.mul_pos hM hk
  obtain ⟨K,C,hK,hCp,H⟩ := widePair_finite_unit_slope_smooth_count D ((2*N+M)*k) (4*N*k+21)
    (4*N*k+16) (2*M*k) hD (by nlinarith only [hN,hNk,Nat.zero_le (M*k)])
    (by nlinarith only [hMk]) (by omega) (by unfold widePairScale; ring)
    (by omega) (by nlinarith only [hMkp]) (finite_local_parametric_budget D N M k hD hM hC)
  have ht : widePairScale ((2*N+M)*k)=4*(2*N+M)*k+20 := by unfold widePairScale; ring
  rw [ht] at H
  exact eventual_single_log_count_of_fixed_enlargement _ _ K C (by omega) hCp H

/-- Every exponent below approximately 0.5293036084 is supplied. -/
theorem infinite_g_gt_finite_local_limit (γ : ℝ) (hγ : γ < 2303/4351) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  have hgap0 : 0 < 2303-4351*γ := by linarith only [hγ]
  obtain ⟨D,hD⟩ := exists_nat_gt (max 2 (255*(1-γ)/(2303-4351*γ)))
  have hD2R : (2 : ℝ) < D := (le_max_left _ _).trans_lt hD
  have hD2 : 2 ≤ D := by exact_mod_cast hD2R.le
  have hlargeD := (div_lt_iff₀ hgap0).mp ((le_max_right _ _).trans_lt hD)
  let N := 2048*D
  let M := 255*(D-1)
  have hN : 22 ≤ N := by dsimp [N]; omega
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hMN : M ≤ N := by dsimp [M,N]; omega
  have hC : (2048/255 : ℝ)*Sieve.localAverageConstant D=(N : ℝ)/(M : ℝ) := by
    simp only [Sieve.localAverageConstant,N,M,Nat.cast_mul,Nat.cast_ofNat,
      Nat.cast_sub (show 1 ≤ D by omega),Nat.cast_one]
    have hd1 : (D : ℝ)-1 ≠ 0 := ne_of_gt (by linarith)
    field_simp
  have hgap : 0 < ((N : ℝ)+M)-γ*(2*(N : ℝ)+M) := by
    simp only [N,M,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (show 1 ≤ D by omega),Nat.cast_one]
    nlinarith only [hlargeD]
  obtain ⟨k,hk⟩ := exists_nat_gt (max 1 ((1+20*γ)/(4*(((N : ℝ)+M)-γ*(2*(N : ℝ)+M)))))
  have hk1R : (1 : ℝ)<k := (le_max_left _ _).trans_lt hk
  have hk1 : 1 ≤ k := by exact_mod_cast hk1R.le
  have hlargek := (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ)<4) hgap)).mp
    ((le_max_right _ _).trans_lt hk)
  obtain ⟨C,hCp,H⟩ := exists_finite_local_parametric_count D N M k hD2 hN hM hMN hk1 hC
  apply infinite_g_gt_of_single_log_smooth_count (4*(2*N+M)*k+20) (4*N*k+21) C
    (by nlinarith [Nat.le_mul_of_pos_right N hk1,Nat.zero_le (M*k)]) H γ
  have ht : (0 : ℝ) < (4*(2*N+M)*k+20 : ℕ) := by positivity
  have hh : ((4*N*k+21 : ℕ) : ℝ)/((4*(2*N+M)*k+20 : ℕ) : ℝ) < 1-γ := by
    apply (div_lt_iff₀ ht).mpr
    push_cast
    nlinarith only [hlargek]
  linarith only [hh]

theorem erdos_821_finite_local_range (ε : ℝ) (hε : 2048/4351 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_finite_local_limit (1-ε) (by linarith only [hε])

theorem infinite_g_gt_point_five_two_nine_three :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(5293/10000 : ℝ)}.Infinite :=
  infinite_g_gt_finite_local_limit _ (by norm_num)

lemma finite_local_limit_improves_three :
    (29599/56223 : ℝ) < 2303/4351 := by norm_num

end Erdos821
