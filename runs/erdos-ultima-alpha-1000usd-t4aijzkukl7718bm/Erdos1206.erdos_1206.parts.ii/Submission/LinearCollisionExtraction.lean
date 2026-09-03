import Submission.CubicScaleBounds
import Submission.RelativeCompactness

/-! A conditional reduction: a positive-density source with uniformly linear
cubic collision counts suffices. No source with that bound is constructed. -/
namespace Erdos1206.LinearCollisionExtraction
open Finset CubicHypergraph HypergraphHubTrimming CubicSamplingStage CubicScaleBounds
open scoped BigOperators Classical

lemma sourcePrefix_card (S : Set ℕ) (N : ℕ) :
    (sourcePrefix S N).card=(S ∩ Set.Iio N).ncard := by
  have he : S ∩ Set.Iio N=(sourcePrefix S N : Set ℕ) := by
    ext n
    simp only [sourcePrefix,Set.mem_inter_iff,Set.mem_Iio,mem_coe,mem_filter,mem_range]
    tauto
  rw [he,Set.ncard_coe_finset]

/-- This is a sufficient arithmetic hypothesis, not a settlement: the
existence of `S,C` satisfying it remains to be established. -/
theorem linear_collision_source_subset (S : Set ℕ) (hS : 0 < S.lowerDensity)
    (C : ℕ) (hC : ∀ N, (edges N S).card ≤ C*N) :
    ∃ A : Set ℕ, A ⊆ S ∧ A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun n : ℕ => n^3) '' A) := by
  obtain ⟨δ,hδ,C₀,hdensity⟩ := Erdos1206.prefix_bound_of_positive_lowerDensity hS
  have hd (n : ℕ) : δ*n ≤ ((sourcePrefix S n).card:ℝ)+C₀ := by
    rw [sourcePrefix_card]
    exact hdensity n
  obtain ⟨k,hk⟩ := exists_nat_gt (16*(C:ℝ)/δ+1)
  have hCnon : 0 ≤ 16*(C:ℝ)/δ := by positivity
  have hkR : (1:ℝ) < k := by linarith
  have hk0 : 0 < k := by exact_mod_cast (zero_lt_one.trans hkR)
  letI : NeZero k := ⟨hk0.ne'⟩
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk0
  have hchoice : 16*(C:ℝ) ≤ δ*(k:ℝ)^2 := by
    have hck : 16*(C:ℝ) < (k:ℝ)*δ := (div_lt_iff₀ hδ).mp (by linarith : 16*(C:ℝ)/δ < k)
    have hks : (k:ℝ) ≤ (k:ℝ)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hks hδ.le]
  let ε := δ/(16*k)
  have hε : 0 < ε := div_pos hδ (by positivity)
  have heq : 16*ε*k=δ := by dsimp only [ε]; field_simp
  have hmean : (C:ℝ)/(k:ℝ)^3 ≤ ε := by
    apply (div_le_iff₀ (pow_pos hkpos 3)).mpr
    nlinarith only [hchoice,congrArg (fun x : ℝ => x*(k:ℝ)^2) heq]
  let B₀ := 16*C^2*CubicPairCodegree.codegreeConstant
  let K : ℝ := (4*C+1)/ε^2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  obtain ⟨jS,hjS⟩ := exists_nat_gt (2*C₀/δ)
  obtain ⟨jB,hjB⟩ := exists_nat_gt ((B₀:ℝ)/ε)
  obtain ⟨jK,hjK⟩ := exists_nat_gt (2*K)
  let j₀ := jS+jB+jK
  have hsource (j : ℕ) (hj : j₀ ≤ j) :
      8*ε*(k:ℝ)*cutoff j ≤ (sourcePrefix S (cutoff j)).card := by
    have hjs : (jS:ℝ) ≤ cutoff j := by
      exact_mod_cast (show jS ≤ j by dsimp only [j₀] at hj; omega).trans (le_cutoff j)
    have hbig : 2*C₀ ≤ (cutoff j:ℝ)*δ := (div_le_iff₀ hδ).mp (hjS.le.trans hjs)
    nlinarith [hd (cutoff j)]
  have hbad (j : ℕ) (hj : j₀ ≤ j) :
      ((bad (edges (cutoff j) S) (hubs (edges (cutoff j) S) (threshold j))).card:ℝ) ≤ ε*cutoff j := by
    have hjb : (jB:ℝ) ≤ (2:ℝ)^j := by
      exact_mod_cast (show jB ≤ j by dsimp only [j₀] at hj; omega).trans (Nat.lt_two_pow_self (n := j)).le
    have hbig : (B₀:ℝ) ≤ ε*(2:ℝ)^j := by
      have hh := (div_le_iff₀ hε).mp (hjB.le.trans hjb)
      linarith
    have hh : ((bad (edges (cutoff j) S) (hubs (edges (cutoff j) S) (threshold j))).card:ℝ) ≤ (B₀:ℝ)*((2:ℝ)^j)^5 := by
      exact_mod_cast bad_bound S (hC (cutoff j))
    have hpow : ((2:ℝ)^j)^6 ≤ ((2:ℝ)^j)^12 :=
      pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega)
    have hm := mul_le_mul_of_nonneg_right hbig (show (0:ℝ) ≤ ((2:ℝ)^j)^5 by positivity)
    have hp := mul_le_mul_of_nonneg_left hpow hε.le
    have hn : (cutoff j:ℝ)=((2:ℝ)^j)^12 := by simp [cutoff]
    rw [hn]
    nlinarith only [hh,hm,hp]
  have hbudget (J : ℕ) : ∑ j∈Ico j₀ (J+1),
      ((cutoff j:ℝ)+4*(edges (cutoff j) S).card*threshold j)/(ε*cutoff j)^2 < 1 := by
    have hjk : (jK:ℝ) ≤ (2:ℝ)^j₀ := by
      exact_mod_cast (show jK ≤ j₀ by dsimp only [j₀]; omega).trans (Nat.lt_two_pow_self (n := j₀)).le
    have hbig : 2*K < (2:ℝ)^j₀ := hjK.trans_le hjk
    calc
      _ ≤ ∑ j∈Ico j₀ (J+1), K*(1/2:ℝ)^j :=
        sum_le_sum (fun j _ => budget_bound S (hC (cutoff j)))
      _ = K*∑ j∈Ico j₀ (J+1), (1/2:ℝ)^j := (mul_sum _ _ _).symm
      _ ≤ K*((1/2:ℝ)^j₀/(1-1/2)) := mul_le_mul_of_nonneg_left
        (geom_sum_Ico_le_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)) hK
      _ = (2*K)/(2:ℝ)^j₀ := by rw [one_div_pow]; ring
      _ < 1 := (div_lt_one (by positivity)).mpr hbig
  apply Erdos1206.existence_of_finite_prefix_construction_in (T := S) (δ := ε/1024)
    (C := (ε/1024)*cutoff j₀) (by positivity)
  intro L
  let J := L+j₀
  have hJM : L ≤ cutoff J := (show L ≤ J by dsimp [J]; omega).trans (le_cutoff J)
  have hmeanGrid (j : ℕ) : ((edges (cutoff j) S).card:ℝ)/(k:ℝ)^3 ≤ ε*cutoff j := by
    have hc : ((edges (cutoff j) S).card:ℝ) ≤ (C:ℝ)*cutoff j := by exact_mod_cast hC (cutoff j)
    calc
      _ ≤ ((C:ℝ)*cutoff j)/(k:ℝ)^3 := div_le_div_of_nonneg_right hc (by positivity)
      _ = ((C:ℝ)/(k:ℝ)^3)*cutoff j := by ring
      _ ≤ ε*cutoff j := mul_le_mul_of_nonneg_right hmean (by positivity)
  obtain ⟨B,hB,hSidon,hgrid⟩ := finite_stage_in_source (M := cutoff J) (k := k) S (Ico j₀ (J+1)) cutoff threshold hε
    (fun j hj => cutoff_mono (by have := (mem_Ico.mp hj).2; omega))
    (fun j _ => cutoff_pos j)
    (fun j hj => hsource j (mem_Ico.mp hj).1)
    (fun j _ => hmeanGrid j) (fun j hj => hbad j (mem_Ico.mp hj).1) (hbudget J)
  refine ⟨B,?_,hSidon,fun n hn => interpolate B hε.le hgrid n (hn.trans hJM)⟩
  intro n hn
  exact (mem_filter.mp (hB hn)).2

/-- The original existential interface. The stronger theorem also preserves
membership in the source. -/
theorem linear_collision_source_suffices (S : Set ℕ) (hS : 0 < S.lowerDensity)
    (C : ℕ) (hC : ∀ N, (edges N S).card ≤ C*N) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun n : ℕ => n^3) '' A) := by
  obtain ⟨A,_,hA⟩ := linear_collision_source_subset S hS C hC
  exact ⟨A,hA⟩

#print axioms linear_collision_source_subset
#print axioms linear_collision_source_suffices
end Erdos1206.LinearCollisionExtraction
