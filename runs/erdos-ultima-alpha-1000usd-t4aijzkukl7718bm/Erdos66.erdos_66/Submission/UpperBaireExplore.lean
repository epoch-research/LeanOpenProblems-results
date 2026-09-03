import Submission.UpperExtensionExplore
import Submission.AnnulusBaireExplore

/-! Saturating annuli and holes coexist even under an exact global upper bound.
This is not a disproof of Erdos 66. -/
namespace Erdos66UpperBaire
open Filter AdditiveCombinatorics Erdos66Compactness Erdos66UpperExtension Erdos66Explore
open scoped Topology Classical

noncomputable def envelope (c : ℝ) : Set (ℕ → Bool) :=
  {f | ∀ n : ℕ, encodedRep f n / Real.log n ≤ c}

lemma envelope_closed (c : ℝ) : IsClosed (envelope c) := by
  simp only [envelope, Set.setOf_forall]
  exact isClosed_iInter (fun n ↦ isClosed_le ((continuous_encodedRep n).div_const _) continuous_const)

instance envelope_compact (c : ℝ) : CompactSpace (envelope c) :=
  isCompact_iff_compactSpace.mp (envelope_closed c).isCompact

lemma envelope_nonempty (c : ℝ) (hc : 0 ≤ c) : Nonempty (envelope c) := by
  refine ⟨⟨fun _ ↦ false, ?_⟩⟩
  intro n
  simpa [encodedRep] using hc

lemma dense_of_prefix_extensions (c : ℝ) (S : Set (envelope c))
    (hS : ∀ f : envelope c, ∀ L : ℕ, ∃ g ∈ S, ∀ i < L, g.val i = f.val i) : Dense S := by
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨f, hf⟩
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨W, ⟨x, L, rfl⟩, hfW, hWV⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ ↦ Bool)).exists_subset_of_mem_open hf hV
  obtain ⟨g, hg, hgf⟩ := hS f L
  refine ⟨g, hWV ?_, hg⟩
  intro i hi
  exact (hgf i hi).trans (hfW i hi)

noncomputable def good (c : ℝ) (k : ℕ) : Set (envelope c) :=
  {f | ∃ N ≥ max k 2, ∀ n ∈ Finset.Icc N ((k + 1) * N),
    |encodedRep f.val n / Real.log n - c| < 1 / ((k : ℝ) + 2)}

lemma good_open (c : ℝ) (k : ℕ) : IsOpen (good c k) := by
  have he : good c k = ⋃ (N : ℕ) (_ : max k 2 ≤ N),
      ⋂ n ∈ Finset.Icc N ((k + 1) * N),
        {f : envelope c | |encodedRep f.val n / Real.log n - c| < 1 / ((k : ℝ) + 2)} := by
    ext f
    simp [good]
  rw [he]
  apply isOpen_iUnion
  intro N
  apply isOpen_iUnion
  intro hN
  apply isOpen_biInter_finset
  intro n hn
  exact isOpen_lt ((((continuous_encodedRep n).comp continuous_subtype_val).div_const _).sub
    continuous_const).abs continuous_const

lemma truncate_envelope (c : ℝ) (f : envelope c) (L : ℕ) :
    ∀ n : ℕ, (sumRep {i | i < L ∧ f.val i = true} n : ℝ) / Real.log n ≤ c := by
  intro n
  have hh := f.property n
  rw [encodedRep_eq_sumRep] at hh
  have hmono := sumRep_mono (show {i | i < L ∧ f.val i = true} ⊆ {i | f.val i = true}
    from fun _ hi ↦ hi.2) n
  have hmono' : (sumRep {i | i < L ∧ f.val i = true} n : ℝ) ≤
      sumRep {i | f.val i = true} n := by exact_mod_cast hmono
  exact (div_le_div_of_nonneg_right hmono' (Real.log_natCast_nonneg n)).trans hh

lemma good_dense (c : ℝ) (hc : 0 < c) (k : ℕ) : Dense (good c k) := by
  apply dense_of_prefix_extensions
  intro f L
  let B : Set ℕ := {i | i < L ∧ f.val i = true}
  obtain ⟨N, hN, hNp, A, hAfin, hBA, hpref, hup, hgood⟩ := exists_upper_extension B L
    (fun _ hi ↦ hi.1) c (1 / ((k : ℝ) + 2)) hc (by positivity)
    (truncate_envelope c f L) (k + 1) (max k 2) (by omega)
  let g : envelope c := ⟨fun i ↦ decide (i ∈ A), by
    intro n
    rw [encodedRep_decide]
    exact hup n⟩
  refine ⟨g, ?_, ?_⟩
  · refine ⟨N, hN, ?_⟩
    intro n hn
    change |encodedRep (fun i ↦ decide (i ∈ A)) n / Real.log n - c| < _
    rw [encodedRep_decide]
    exact hgood n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
  · intro i hi
    have hh := hpref i hi
    change decide (i ∈ A) = f.val i
    simp only [B, Set.mem_setOf_eq, hi, true_and] at hh
    cases hfi : f.val i <;> simp_all

noncomputable def hole (c : ℝ) (k : ℕ) : Set (envelope c) :=
  {f | ∃ n ≥ k, encodedRep f.val n < 1}

lemma hole_open (c : ℝ) (k : ℕ) : IsOpen (hole c k) := by
  have he : hole c k = ⋃ (n : ℕ) (_ : k ≤ n), {f : envelope c | encodedRep f.val n < 1} := by
    ext f
    simp [hole]
  rw [he]
  apply isOpen_iUnion
  intro n
  apply isOpen_iUnion
  intro hn
  exact isOpen_lt ((continuous_encodedRep n).comp continuous_subtype_val) continuous_const

lemma hole_dense (c : ℝ) (k : ℕ) : Dense (hole c k) := by
  apply dense_of_prefix_extensions
  intro f L
  let A : Set ℕ := {i | i < L ∧ f.val i = true}
  have hAfin : A.Finite := (Set.finite_Iio L).subset (fun _ hi ↦ hi.1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp (sumRep_eventually_zero_of_finite hAfin)
  let g : envelope c := ⟨fun i ↦ decide (i ∈ A), by
    intro n
    simp only [encodedRep_eq_sumRep, decide_eq_true_eq]
    exact truncate_envelope c f L n⟩
  refine ⟨g, ?_, ?_⟩
  · refine ⟨max k M, le_max_left _ _, ?_⟩
    change encodedRep (fun i ↦ decide (i ∈ A)) (max k M) < 1
    simp only [encodedRep_eq_sumRep, decide_eq_true_eq]
    change (sumRep A (max k M) : ℝ) < 1
    rw [hM _ (le_max_right _ _)]
    norm_num
  · intro i hi
    change decide (i ∈ A) = f.val i
    simp only [A, Set.mem_setOf_eq, hi, true_and]
    cases f.val i <;> rfl

lemma dense_saturating_annuli_and_holes (c : ℝ) (hc : 0 < c) :
    Dense (⋂ k, good c k ∩ hole c k) :=
  dense_iInter_of_isOpen_nat (fun k ↦ (good_open c k).inter (hole_open c k))
    (fun k ↦ (good_dense c hc k).inter_of_isOpen_right (hole_dense c k) (hole_open c k))

/-- Even an exact global upper envelope, together with annuli saturating it at
every accuracy and length, does not rule out arbitrarily late holes. -/
theorem exists_upper_annuli_and_holes (c : ℝ) (hc : 0 < c) : ∃ A : Set ℕ,
    (∀ n : ℕ, (sumRep A n : ℝ) / Real.log n ≤ c) ∧
    (∀ (ε : ℝ), 0 < ε → ∀ R N₀ : ℕ, 1 ≤ R →
      ∃ N ≥ N₀, 0 < N ∧ ∀ n : ℕ, N ≤ n → n ≤ R * N →
        |(sumRep A n : ℝ) / Real.log n - c| < ε) ∧
    (∀ K : ℕ, ∃ n ≥ K, sumRep A n = 0) := by
  letI := envelope_nonempty c hc.le
  obtain ⟨f, hf⟩ := (dense_saturating_annuli_and_holes c hc).nonempty
  let A : Set ℕ := {i | f.val i = true}
  refine ⟨A, ?_, ?_, ?_⟩
  · intro n
    simpa only [encodedRep_eq_sumRep] using f.property n
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

/-- The preceding upper-bounded examples have no limit at any real constant.
This theorem is existential in A, unlike a disproof of the original conjecture. -/
theorem exists_upper_annular_nonconvergent (c : ℝ) (hc : 0 < c) : ∃ A : Set ℕ,
    (∀ n : ℕ, (sumRep A n : ℝ) / Real.log n ≤ c) ∧
    (∀ (ε : ℝ), 0 < ε → ∀ R N₀ : ℕ, 1 ≤ R →
      ∃ N ≥ N₀, 0 < N ∧ ∀ n : ℕ, N ≤ n → n ≤ R * N →
        |(sumRep A n : ℝ) / Real.log n - c| < ε) ∧
    ∀ d : ℝ, ¬Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 d) := by
  obtain ⟨A, hu, hg, hh⟩ := exists_upper_annuli_and_holes c hc
  refine ⟨A, hu, hg, ?_⟩
  intro d hd
  by_cases hd0 : d = 0
  · subst d
    obtain ⟨P, hP⟩ := Metric.tendsto_atTop.mp hd (c / 4) (by positivity)
    obtain ⟨N, hN, hNp, hgood⟩ := hg (c / 2) (by positivity) 1 P le_rfl
    have h₁ := hP N hN
    have h₂ := hgood N le_rfl (by omega)
    rw [Real.dist_eq, sub_zero] at h₁
    have h₁' := (abs_lt.mp h₁).2
    have h₂' := (abs_lt.mp h₂).1
    linarith
  · exact Erdos66AnnulusBaire.no_nonzero_limit_of_holes A hh d hd0 hd

end Erdos66UpperBaire
