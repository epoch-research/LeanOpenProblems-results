import Submission.CorrelationVaughan
import Submission.CenteredRowScales

/-! Vaughan's identity with the common Chebyshev center. Both Type-I terms
are small at arbitrarily large common scales for every irrational slope.
The two-Mangoldt Type-II term remains explicit. -/
namespace Erdos972CenteredVaughan

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta Topology
open Erdos972Vaughan Erdos972PrimePowerError Erdos972ChebyshevRowMean Erdos972SelfCenteredLog
open Erdos972CorrelationVaughan Erdos972CenteredRowScales Erdos972ExponentialSum

noncomputable def centeredOutput (α ρ : ℝ) (n : ℕ) := vonMangoldt (floorMul α n)-ρ

noncomputable def first (α ρ : ℝ) (U N : ℕ) :=
  ∑ m ∈ Ioc 0 (min U N), (μ m : ℝ)*
    ∑ n ∈ Ioc 0 (N/m), Real.log n*centeredOutput α ρ (m*n)

noncomputable def second (α ρ : ℝ) (U V N : ℕ) :=
  ∑ m ∈ Ioc 0 (min (U*V) N), (cutoff (μ : ArithmeticFunction ℝ) U*cutoff Λ V) m*
    ∑ n ∈ Ioc 0 (N/m), centeredOutput α ρ (m*n)

noncomputable def bilinear (α ρ : ℝ) (U V N : ℕ) :=
  ∑ m ∈ Ioc 0 N, (tail (μ : ArithmeticFunction ℝ) U*ζ) m*
    ∑ n ∈ Ioc 0 (N/m), tail Λ V n*centeredOutput α ρ (m*n)

noncomputable def small (α ρ : ℝ) (V N : ℕ) := weightedSum (cutoff Λ V) (centeredOutput α ρ) N

lemma first_eq (α ρ : ℝ) (U N : ℕ) :
    weightedSum (cutoff (μ : ArithmeticFunction ℝ) U*ArithmeticFunction.log) (centeredOutput α ρ) N = first α ρ U N := by
  rw [weightedSum_convolution_support _ _ _ U N (fun n hn => cutoff_eq_zero_of_lt _ hn)]
  apply sum_congr rfl
  intro m hm
  rw [cutoff_eq_of_le _ ((mem_Ioc.mp hm).2.trans (min_le_left _ _))]
  rfl

lemma second_eq (α ρ : ℝ) (U V N : ℕ) :
    weightedSum (cutoff (μ : ArithmeticFunction ℝ) U*ζ*cutoff Λ V) (centeredOutput α ρ) N = second α ρ U V N := by
  have he : cutoff (μ : ArithmeticFunction ℝ) U*ζ*cutoff Λ V =
      (cutoff (μ : ArithmeticFunction ℝ) U*cutoff Λ V)*ζ := by ring
  rw [he, weightedSum_convolution_support _ _ _ (U*V) N
    (fun n hn => cutoff_mul_cutoff_eq_zero_of_lt _ _ U V n hn)]
  apply sum_congr rfl
  intro m hm
  congr 1
  apply sum_congr rfl
  intro n hn
  simp only [natCoe_apply, zeta_apply_ne (Nat.ne_of_gt (mem_Ioc.mp hn).1), Nat.cast_one, one_mul]

/-- The exact two-prime correlation identity, with a free scalar center. -/
theorem centered_vaughan_identity (α ρ : ℝ) (U V N : ℕ) :
    mangoldtCorrelation α N-ρ*Chebyshev.psi N =
      first α ρ U N-second α ρ U V N+small α ρ V N+bilinear α ρ U V N := by
  have hh := congrArg (fun f => weightedSum f (centeredOutput α ρ) N) (vaughan_identity U V)
  simp only [weightedSum_add, weightedSum_sub, first_eq, second_eq] at hh
  have he : weightedSum Λ (centeredOutput α ρ) N = mangoldtCorrelation α N-ρ*Chebyshev.psi N := by
    simp only [weightedSum, centeredOutput, mul_sub, sum_sub_distrib, ← sum_mul,
      mangoldtCorrelation, Chebyshev.psi, Nat.floor_natCast]
    ring
  rw [he, weightedSum_convolution] at hh
  exact hh

lemma centeredOutput_row (α ρ : ℝ) (m n : ℕ) :
    centeredOutput α ρ (m*n) = vonMangoldt (floorMul (α*m) n)-ρ := by
  simp only [centeredOutput, floorMul, Nat.cast_mul, mul_assoc]

lemma first_bound (α ρ ε : ℝ) (hε : 0 ≤ ε) (U N : ℕ)
    (hrows : ∀ m ∈ Ioc 0 U,
      |centeredLogRow (fun n => vonMangoldt (floorMul (α*m) n)) ρ (N/m)| ≤ ε*N) :
    |first α ρ U N| ≤ (U : ℝ)*ε*N := by
  unfold first
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ m ∈ Ioc 0 (min U N), ε*N := by
      apply sum_le_sum
      intro m hm
      have hmU : m ∈ Ioc 0 U := mem_Ioc.mpr ⟨(mem_Ioc.mp hm).1, (mem_Ioc.mp hm).2.trans (min_le_left _ _)⟩
      have hμ : |(μ m : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := m)
      rw [abs_mul]
      simp only [centeredOutput_row]
      have hh := hrows m hmU
      unfold centeredLogRow at hh
      exact (mul_le_mul hμ hh (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = (min U N : ℕ)* (ε*N) := by simp
    _ ≤ _ := by
      have hh : ((min U N : ℕ) : ℝ) ≤ U := Nat.cast_le.mpr (min_le_left U N)
      nlinarith [mul_nonneg hε (Nat.cast_nonneg (α := ℝ) N)]

lemma second_bound (α ρ ε : ℝ) (hε : 0 ≤ ε) (U V N : ℕ)
    (hrows : ∀ m ∈ Ioc 0 (U*V),
      |∑ n ∈ Ioc 0 (N/m), (vonMangoldt (floorMul (α*m) n)-ρ)| ≤ ε*N) :
    |second α ρ U V N| ≤ ((U*V : ℕ) : ℝ)*Real.log (U*V : ℕ)*ε*N := by
  unfold second
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ m ∈ Ioc 0 (min (U*V) N), Real.log (U*V : ℕ)*(ε*N) := by
      apply sum_le_sum
      intro m hm
      have hmUV : m ∈ Ioc 0 (U*V) := mem_Ioc.mpr ⟨(mem_Ioc.mp hm).1, (mem_Ioc.mp hm).2.trans (min_le_left _ _)⟩
      rw [abs_mul]
      simp only [centeredOutput_row]
      exact mul_le_mul ((abs_typeI_coefficient_le_log U V m).trans
        (monotone_log_natCast (mem_Ioc.mp hmUV).2)) (hrows m hmUV) (abs_nonneg _) (Real.log_natCast_nonneg _)
    _ = (min (U*V) N : ℕ)*(Real.log (U*V : ℕ)*(ε*N)) := by simp
    _ ≤ _ := by
      have hh : ((min (U*V) N : ℕ) : ℝ) ≤ (U*V : ℕ) := Nat.cast_le.mpr (min_le_left _ _)
      have hpos : 0 ≤ Real.log (U*V : ℕ)*(ε*N) := by positivity [Real.log_natCast_nonneg (U*V)]
      nlinarith [mul_le_mul_of_nonneg_right hh hpos]

lemma small_bound {α : ℝ} (hα : 1 ≤ α) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ7 : ρ ≤ 7)
    (V : ℕ) {N : ℕ} (hN : 0 < N) :
    |small α ρ V N| ≤ Chebyshev.psi V*(Real.log (α*N)+7) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (α*N)+7 := by
    have := Real.log_nonneg (show 1 ≤ α*N by nlinarith)
    linarith
  have herr (n : ℕ) (hn : n ∈ Ioc 0 N) : |centeredOutput α ρ n| ≤ Real.log (α*N)+7 := by
    unfold centeredOutput
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg vonMangoldt_nonneg, abs_of_nonneg hρ0]
    have hh := (vonMangoldt_le_log (n := floorMul α n)).trans (log_floorMul_le hα hn)
    linarith
  unfold small weightedSum
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, cutoff Λ V n*(Real.log (α*N)+7) := by
      apply sum_le_sum
      intro n hn
      rw [abs_mul, abs_of_nonneg (cutoff_vonMangoldt_nonneg V n)]
      exact mul_le_mul_of_nonneg_left (herr n hn) (cutoff_vonMangoldt_nonneg V n)
    _ = (∑ n ∈ Ioc 0 (min V N), Λ n)*(Real.log (α*N)+7) := by
      rw [← sum_mul]
      congr 1
      simp only [cutoff_apply, ← sum_filter]
      congr 1
      ext n
      simp only [mem_filter, mem_Ioc, le_min_iff]
      tauto
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hlog
      simpa only [Chebyshev.psi, Nat.floor_natCast] using Chebyshev.psi_mono (Nat.cast_le.mpr (min_le_left V N))

noncomputable def typeICoefficient (U V : ℕ) : ℝ := (U : ℝ)+(U*V : ℕ)*Real.log (U*V : ℕ)

lemma typeICoefficient_nonneg (U V : ℕ) : 0 ≤ typeICoefficient U V := by
  unfold typeICoefficient
  positivity [Real.log_natCast_nonneg (U*V)]

/-- The two centered Type-I terms are simultaneously small at arbitrarily large
cutoffs for each fixed pair of Vaughan parameters. -/
theorem exists_small_typeI {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (U V : ℕ) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ N : ℕ, B < N ∧ |first α (commonMean α N) U N|+|second α (commonMean α N) U V N| ≤ ε*N := by
  let C := typeICoefficient U V
  have hC : 0 ≤ C := typeICoefficient_nonneg U V
  let η := ε/(C+1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N, hN, hrows⟩ := exists_common_centered_row_scale hα hI (max U (U*V)) hη B
  have hrow1 (m : ℕ) (hm : m ∈ Ioc 0 U) := (hrows m (mem_Ioc.mpr ⟨(mem_Ioc.mp hm).1,
    (mem_Ioc.mp hm).2.trans (le_max_left _ _)⟩)).2
  have hrow2 (m : ℕ) (hm : m ∈ Ioc 0 (U*V)) := (hrows m (mem_Ioc.mpr ⟨(mem_Ioc.mp hm).1,
    (mem_Ioc.mp hm).2.trans (le_max_right _ _)⟩)).1
  have hf := first_bound α (commonMean α N) η hη.le U N hrow1
  have hs := second_bound α (commonMean α N) η hη.le U V N hrow2
  have hηC : C*η ≤ ε := by
    dsimp [η]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < C+1 by linarith)).mpr
    nlinarith
  refine ⟨N, hN, ?_⟩
  calc
    _ ≤ C*η*N := by dsimp [C, typeICoefficient]; linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hηC (Nat.cast_nonneg N)

#print axioms centered_vaughan_identity
#print axioms exists_small_typeI
#print axioms small_bound

end Erdos972CenteredVaughan
