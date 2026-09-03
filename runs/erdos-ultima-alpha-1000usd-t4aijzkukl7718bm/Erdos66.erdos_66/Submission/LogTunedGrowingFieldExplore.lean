import Submission.FiniteFieldDegreeExplore
import Submission.OddDegreeLogTuningExplore

/-! A finite-field growing-slice construction with a fixed logarithmic
coefficient. Its modulus is the cardinality of a field plane, not an ordinary
natural-prefix cutoff. No integer-carry or infinite-limit theorem is asserted. -/
namespace Erdos66LogTunedGrowingField
open Filter Erdos66FiniteFieldDegree Erdos66OddDegreeLogTuning
  Erdos66GrowingSubfieldBlock Erdos66OddExtensionFlatSet
  Erdos66FiniteField Erdos66OriginRepair Erdos66ParabolaRepair Erdos66Coset
open scoped Classical Topology
set_option maxHeartbeats 2800000
universe u

lemma normalized_error (r μ L c ε τ : ℝ) (hL : 0<L) (hε : 0≤ε)
    (hrep : |r-μ|≤ε*μ) (hbelow : 0≤c-μ/L) (htune : c-μ/L≤τ) :
    |r/L-c|≤ε*c+τ := by
  have hround : |r/L-μ/L|≤ε*c := by
    rw [←sub_div,abs_div,abs_of_pos hL]
    have hh := div_le_div_of_nonneg_right hrep hL.le
    have ht := mul_le_mul_of_nonneg_left (show μ/L≤c by linarith) hε
    rw [mul_div_assoc] at hh
    exact hh.trans ht
  have hscalar : |μ/L-c|≤τ := by
    rw [abs_sub_comm,abs_of_nonneg hbelow]
    exact htune
  exact (abs_sub_le (r/L) (μ/L) c).trans (by linarith)

/-- The coefficient and precision precede the old field and its model.
A larger ACTUAL finite field, its algebra structure, and its actual set are
constructed. The exact old repaired field-plane slice is retained. -/
theorem exists_log_tuned_growing_extension (c δ : ℝ) (hc : 0<c) (hδ : 0<δ) :
    ∃ ε : ℝ, 0<ε ∧ ε≤1 ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ringChar F≠2 → N≤Fintype.card F →
      ∀ U : Finset F, U.Nonempty → (∀ a∈U, a≠0) →
        (∀ a∈U, ∀ b∈U, a+b≠0) → 10*(U.card:ℝ)≤ε*Fintype.card F →
      ∀ w : F, w≠0 → w∉U → -w∉U →
      ∀ T : Finset F, (0:F)∉T →
      ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : DecidableEq K)
        (_ : Algebra F K) (B : Finset (K×K)),
        Odd (Module.finrank F K) ∧ (Fintype.card F)^3≤Fintype.card K ∧
        (∀ z : F×F, planeMap z∈B ↔ z∈parabolaSet U∪repairPoints w T) ∧
        ∀ z : K×K, |(pairCount B B z:ℝ)/Real.log (((Fintype.card K)^2:ℕ):ℝ)-c|≤δ := by
  let ε := min 1 (δ/(2*c))
  have hε : 0<ε := by dsimp [ε]; positivity
  have hε1 : ε≤1 := min_le_left _ _
  have hcost : ε*c≤δ/2 := by
    have hh := (le_div_iff₀ (by positivity : 0<2*c)).mp (min_le_right 1 (δ/(2*c)))
    dsimp only [ε]
    nlinarith only [hh]
  obtain ⟨L,hL⟩ := eventually_atTop.mp
    ((tuning_cost_tendsto_zero c).eventually_le_const (show (0:ℝ)<δ/2 by positivity))
  let P := ⌈1600/ε^2⌉₊
  let N := max 3 (max L P)
  refine ⟨ε,hε,hε1,N,?_⟩
  intro F _ _ _ hF hN U hne hU hUU huq w hw hwU hnwU T hT
  let q := Fintype.card F
  have hq : 3≤q := by dsimp [N] at hN; omega
  have hLq : L≤q := by dsimp [N] at hN; omega
  have hPq : P≤q := by dsimp [N] at hN; omega
  have hprecision : 1600≤ε^2*(q:ℝ) := by
    have hh : 1600/ε^2≤(q:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hPq)
    have ht := (div_le_iff₀ (sq_pos_of_pos hε)).mp hh
    nlinarith only [ht]
  obtain ⟨d,hd,hd3,hbelow,htune⟩ := odd_degree_tuning q (by omega) (U.card:ℝ) c
    (Nat.cast_nonneg _) hc
  obtain ⟨K,hfield,hfinite,halgebra,hdegree,hcard,hchar⟩ :=
    exists_extension_degree F d (by omega)
  letI := hfield
  letI := hfinite
  letI := halgebra
  letI : DecidableEq K := Classical.decEq K
  have hK : ringChar K≠2 := by rw [hchar]; exact hF
  have hodd : Odd (Module.finrank F K) := by rw [hdegree]; exact hd
  have hcube : q^3≤Fintype.card K := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by omega : 1≤q) hd3
  obtain ⟨B,hslice,hB⟩ := exists_accurate_subfield_block_extension hodd hK hq hcube
    U hne hU hUU w hw hwU hnwU T hT ε hε hε1 huq hprecision
  refine ⟨K,hfield,hfinite,inferInstance,halgebra,B,hodd,hcube,hslice,?_⟩
  intro z
  have hcl : 1<Fintype.card K := by
    have hh : 1<q^3 := one_lt_pow₀ (by omega : 1<q) (by norm_num)
    omega
  have hlog : 0<Real.log (((Fintype.card K)^2:ℕ):ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by nlinarith : 1<(Fintype.card K)^2)
  change Fintype.card K=q^d at hcard
  rw [←hcard] at hbelow htune
  have ht : c-((U.card:ℝ)+q)^2/Real.log (((Fintype.card K)^2:ℕ):ℝ)≤δ/2 :=
    htune.trans (hL q hLq)
  exact (normalized_error (pairCount B B z) (((U.card:ℝ)+q)^2)
    (Real.log (((Fintype.card K)^2:ℕ):ℝ)) c ε (δ/2) hlog hε.le
    (hB z) hbelow ht).trans (by linarith)

end Erdos66LogTunedGrowingField
