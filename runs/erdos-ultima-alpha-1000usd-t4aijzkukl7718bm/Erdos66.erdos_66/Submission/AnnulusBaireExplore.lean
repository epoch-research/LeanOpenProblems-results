import Submission.AnnulusExtensionExplore
import Submission.CompactnessExplore

/-! The finite annulus theorem does not imply convergence, even after all its
annuli are realized in one set. There is a set with arbitrarily late good
annuli of every accuracy and length, and also arbitrarily late holes. -/
namespace Erdos66AnnulusBaire
open Filter AdditiveCombinatorics Erdos66Compactness Erdos66AnnulusExtension
open scoped Topology Classical

lemma dense_of_prefix_extensions (S : Set (ℕ → Bool))
    (hS : ∀ f : ℕ → Bool, ∀ L : ℕ, ∃ g ∈ S, ∀ i < L, g i = f i) : Dense S := by
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨f, hf⟩
  obtain ⟨V, ⟨x, L, rfl⟩, hfV, hVU⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ ↦ Bool)).exists_subset_of_mem_open hf hU
  obtain ⟨g, hg, hgf⟩ := hS f L
  refine ⟨g, hVU ?_, hg⟩
  intro i hi
  exact (hgf i hi).trans (hfV i hi)

noncomputable def good (k : ℕ) : Set (ℕ → Bool) :=
  {f | ∃ N ≥ max k 2, ∀ n ∈ Finset.Icc N ((k + 1) * N),
    |encodedRep f n / Real.log n - 1| < 1 / ((k : ℝ) + 2)}

lemma good_open (k : ℕ) : IsOpen (good k) := by
  have he : good k = ⋃ (N : ℕ) (_ : max k 2 ≤ N),
      ⋂ n ∈ Finset.Icc N ((k + 1) * N),
        {f : ℕ → Bool | |encodedRep f n / Real.log n - 1| < 1 / ((k : ℝ) + 2)} := by
    ext f
    simp [good]
  rw [he]
  apply isOpen_iUnion
  intro N
  apply isOpen_iUnion
  intro hN
  apply isOpen_biInter_finset
  intro n hn
  exact isOpen_lt (((continuous_encodedRep n).div_const _).sub continuous_const).abs continuous_const

lemma good_dense (k : ℕ) : Dense (good k) := by
  apply dense_of_prefix_extensions
  intro f L
  obtain ⟨N, hN, hNp, A, hAfin, hpref, hgood⟩ := exists_annulus_extension
    {i | f i = true} L (1 / ((k : ℝ) + 2)) (by positivity) (k + 1) (max k 2) (by omega)
  refine ⟨fun i ↦ decide (i ∈ A), ?_, ?_⟩
  · refine ⟨N, hN, ?_⟩
    intro n hn
    rw [encodedRep_decide]
    exact hgood n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
  · intro i hi
    have hh := hpref i hi
    cases hfi : f i <;> simp_all

noncomputable def hole (k : ℕ) : Set (ℕ → Bool) :=
  {f | ∃ n ≥ k, encodedRep f n < 1}

lemma hole_open (k : ℕ) : IsOpen (hole k) := by
  have he : hole k = ⋃ (n : ℕ) (_ : k ≤ n), {f | encodedRep f n < 1} := by
    ext f
    simp [hole]
  rw [he]
  apply isOpen_iUnion
  intro n
  apply isOpen_iUnion
  intro hn
  exact isOpen_lt (continuous_encodedRep n) continuous_const

lemma hole_dense (k : ℕ) : Dense (hole k) := by
  apply dense_of_prefix_extensions
  intro f L
  let A : Set ℕ := {i | i < L ∧ f i = true}
  have hAfin : A.Finite := (Set.finite_Iio L).subset (fun i hi ↦ hi.1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp (Erdos66Explore.sumRep_eventually_zero_of_finite hAfin)
  refine ⟨fun i ↦ decide (i ∈ A), ?_, ?_⟩
  · refine ⟨max k M, le_max_left _ _, ?_⟩
    simp only [encodedRep_eq_sumRep, decide_eq_true_eq]
    change (sumRep A (max k M) : ℝ) < 1
    rw [hM _ (le_max_right _ _)]
    norm_num
  · intro i hi
    simp only [A, Set.mem_setOf_eq, hi, true_and]
    cases f i <;> rfl

lemma dense_good_annuli_and_holes : Dense (⋂ k, good k ∩ hole k) :=
  dense_iInter_of_isOpen_nat (fun k ↦ (good_open k).inter (hole_open k))
    (fun k ↦ (good_dense k).inter_of_isOpen_right (hole_dense k) (hole_open k))

/-- One set can realize all requested annuli and nevertheless have infinitely
many unrepresented integers. In particular, this is not a witness to Erdős 66. -/
theorem exists_good_annuli_and_holes : ∃ A : Set ℕ,
    (∀ (ε : ℝ), 0 < ε → ∀ R N₀ : ℕ, 1 ≤ R →
      ∃ N ≥ N₀, 0 < N ∧ ∀ n : ℕ, N ≤ n → n ≤ R * N →
        |(sumRep A n : ℝ) / Real.log n - 1| < ε) ∧
    (∀ K : ℕ, ∃ n ≥ K, sumRep A n = 0) := by
  obtain ⟨f, hf⟩ := dense_good_annuli_and_holes.nonempty
  let A : Set ℕ := {i | f i = true}
  refine ⟨A, ?_, ?_⟩
  · intro ε hε R N₀ hR
    obtain ⟨J, hJ⟩ := exists_nat_one_div_lt hε
    let k := max J (max R N₀)
    obtain ⟨N, hN, hgood⟩ := (Set.mem_iInter.mp hf k).1
    refine ⟨N, by dsimp [k] at hN; omega, by omega, ?_⟩
    intro n hnlo hnhi
    have hn : n ∈ Finset.Icc N ((k + 1) * N) := by
      apply Finset.mem_Icc.mpr
      constructor
      · exact hnlo
      · have hRk : R ≤ k + 1 := by dsimp [k]; omega
        exact hnhi.trans (Nat.mul_le_mul_right N hRk)
    have hh := hgood n hn
    rw [encodedRep_eq_sumRep] at hh
    have he : 1 / ((k : ℝ) + 2) < ε := by
      have hJk : (J : ℝ) ≤ k := by exact_mod_cast (le_max_left J (max R N₀))
      have hle : 1 / ((k : ℝ) + 2) ≤ 1 / ((J : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        linarith
      exact hle.trans_lt hJ
    exact hh.trans he
  · intro K
    obtain ⟨n, hn, hh⟩ := (Set.mem_iInter.mp hf K).2
    refine ⟨n, hn, ?_⟩
    rw [encodedRep_eq_sumRep] at hh
    exact Nat.cast_lt_one.mp hh

lemma no_nonzero_limit_of_holes (A : Set ℕ)
    (hhole : ∀ K : ℕ, ∃ n ≥ K, sumRep A n = 0) (c : ℝ) (hc : c ≠ 0) :
    ¬Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) := by
  intro hlim
  apply hc
  apply tendsto_nhds_unique_of_frequently_eq hlim tendsto_const_nhds
  apply frequently_atTop.mpr
  intro K
  obtain ⟨n, hn, hh⟩ := hhole K
  refine ⟨n, hn, ?_⟩
  change (sumRep A n : ℝ) / Real.log n = 0
  rw [hh]
  simp only [Nat.cast_zero, zero_div]

lemma no_zero_limit_of_annuli (A : Set ℕ)
    (hgood : ∀ K : ℕ, ∃ n ≥ K, |(sumRep A n : ℝ) / Real.log n - 1| < 1 / 2) :
    ¬Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 (0 : ℝ)) := by
  intro hlim
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hlim (1 / 2) (by norm_num)
  obtain ⟨n, hn, hgood⟩ := hgood K
  have hsmall := hK n hn
  rw [Real.dist_eq, sub_zero] at hsmall
  have h₁ := (abs_lt.mp hgood).1
  have h₂ := (abs_lt.mp hsmall).2
  linarith

/-- Annular approximation at every accuracy, even for one set, does not imply
any limit for the normalized representation function. This does not rule out
a different set satisfying the conjecture. -/
theorem exists_annular_nonconvergent : ∃ A : Set ℕ,
    (∀ (ε : ℝ), 0 < ε → ∀ R N₀ : ℕ, 1 ≤ R →
      ∃ N ≥ N₀, 0 < N ∧ ∀ n : ℕ, N ≤ n → n ≤ R * N →
        |(sumRep A n : ℝ) / Real.log n - 1| < ε) ∧
    (∀ c : ℝ, ¬Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) := by
  obtain ⟨A, hgood, hhole⟩ := exists_good_annuli_and_holes
  refine ⟨A, hgood, fun c ↦ ?_⟩
  by_cases hc : c = 0
  · subst c
    apply no_zero_limit_of_annuli A
    intro K
    obtain ⟨N, hN, hNp, hNGood⟩ := hgood (1 / 2) (by norm_num) 1 K (by omega)
    exact ⟨N, hN, hNGood N le_rfl (by omega)⟩
  · exact no_nonzero_limit_of_holes A hhole c hc

end Erdos66AnnulusBaire
