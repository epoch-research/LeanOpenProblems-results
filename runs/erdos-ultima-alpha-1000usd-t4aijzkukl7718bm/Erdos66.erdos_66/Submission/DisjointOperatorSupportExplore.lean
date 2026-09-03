import Submission.DisjointBlockOperatorExplore
import Submission.FixedTemplateObstructionExplore
import Submission.ResidueSupportMassExplore
import Submission.SaturatingCyclicFamilyExplore

/-! Fixed-support and repair-mass limitations of the disjoint natural operator.
These results do not exclude constructions whose fine palette changes with scale. -/
namespace Erdos66DisjointOperatorSupport
open Filter AdditiveCombinatorics Erdos66DisjointBlockOperator
  Erdos66CyclicThickening Erdos66OriginRepair Erdos66FixedTemplateObstruction
  Erdos66ResidueSupportMass Erdos66Counting
open scoped Classical Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (M : ℕ) [NeZero M]

lemma naturalOperator_supported (K : ℕ) [NeZero K]
    (P : ι → Finset (ZMod M)) (B : ι → Set ℕ) :
    ∀ a ∈ naturalOperator M K P B, (a : ZMod M) ∈ Finset.univ.biUnion P := by
  intro a ha
  obtain ⟨i,hi,hp⟩ := (naturalOperator_mem M K P B a).mp ha
  have he : reduceDigit M K (a : ZMod (M*K))=(a : ZMod M) := map_natCast _ _
  rw [he] at hp
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hp⟩

/-- No coarse-input choice removes a proper fine support. -/
theorem no_proper_support_operator (K : ℕ) [NeZero K]
    (P : ι → Finset (ZMod M)) (hP : Finset.univ.biUnion P≠Finset.univ)
    (B : ι → Set ℕ) :
    ¬ ∃ c : ℝ, c≠0 ∧
      Tendsto (fun n ↦ (sumRep (naturalOperator M K P B) n : ℝ)/Real.log n)
        atTop (𝓝 c) := by
  obtain ⟨z,hz⟩ : ∃ z : ZMod M, z∉Finset.univ.biUnion P := by
    by_contra hh
    push_neg at hh
    exact hP (Finset.eq_univ_of_forall hh)
  apply no_missing_residue M _ z
  intro a ha he
  exact hz (he ▸ naturalOperator_supported M K P B a ha)

/-- A concrete sufficient size condition guarantees that a mixed-flat disjoint
palette cannot cover all residues. -/
lemma palette_proper_of_mean_bound (P : ι → Finset (ZMod M))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j))) (μ η : ℝ)
    (hflat : ∀ i j z, |(pairCount (P i) (P j) z : ℝ)-μ| ≤ η*μ)
    (hbudget : (1+η)*μ*(Fintype.card ι:ℝ)^2<M) :
    Finset.univ.biUnion P≠Finset.univ := by
  intro he
  have hh := selected_union_error P hP Finset.univ Finset.univ (0 : ZMod M) μ (η*μ)
    (fun i hi j hj ↦ hflat i j 0)
  rw [he] at hh
  have hcount : pairCount (Finset.univ : Finset (ZMod M)) Finset.univ 0=M := by
    simp [pairCount]
  rw [hcount] at hh
  simp only [Finset.card_univ] at hh
  have hb := (abs_le.mp hh).2
  nlinarith only [hb,hbudget]

/-- Repairs of a fixed natural operator must supply at least the complement
of its fine support's proportion of total counting mass. -/
theorem operator_repair_mass (K : ℕ) [NeZero K]
    (P : ι → Finset (ZMod M)) (B : ι → Set ℕ) (D : Set ℕ)
    {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep (naturalOperator M K P B ∪ D) n : ℝ)/Real.log n)
      atTop (𝓝 c)) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N in atTop, 1-((Finset.univ.biUnion P).card : ℝ)/M-ε <
      (count D N : ℝ)/count (naturalOperator M K P B ∪ D) N :=
  eventual_repair_fraction M _ D hc ht _ (naturalOperator_supported M K P B) ε hε

/-- Negligible additive corrections cannot fix a proper-support operator. -/
theorem no_negligible_operator_repair (K : ℕ) [NeZero K]
    (P : ι → Finset (ZMod M)) (hP : Finset.univ.biUnion P≠Finset.univ)
    (B : ι → Set ℕ) (D : Set ℕ)
    (hD : Tendsto (fun N ↦ (count D N : ℝ)/count (naturalOperator M K P B ∪ D) N)
      atTop (𝓝 0)) :
    ¬ ∃ c : ℝ, c≠0 ∧
      Tendsto (fun n ↦ (sumRep (naturalOperator M K P B ∪ D) n : ℝ)/Real.log n)
        atTop (𝓝 c) :=
  no_negligible_fixed_support_repair M _ D _ hP (naturalOperator_supported M K P B) hD


/-- The union support has the density dictated by its nominal mixed mean. -/
lemma palette_support_sq_bound (P : ι → Finset (ZMod M))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j))) (μ η : ℝ)
    (hflat : ∀ i j z, |(pairCount (P i) (P j) z : ℝ)-μ| ≤ η*μ) :
    ((Finset.univ.biUnion P).card:ℝ)^2 ≤ M*((1+η)*μ*(Fintype.card ι:ℝ)^2) := by
  have hh := Erdos66SaturatingCyclicFamily.actualMean_error M
    (Finset.univ.biUnion P) (Finset.univ.biUnion P)
    (μ*(Fintype.card ι:ℝ)^2) (η*μ*(Fintype.card ι:ℝ)^2) (fun z ↦ by
      have he := selected_union_error P hP Finset.univ Finset.univ z μ (η*μ)
        (fun i hi j hj ↦ hflat i j z)
      simp only [Finset.card_univ, pairCount, Erdos66OuterCarryProfile.cyclicCount] at he ⊢
      simpa only [pow_two, mul_assoc] using he)
  have hm : (0:ℝ)<M := by exact_mod_cast NeZero.pos M
  have he := (abs_le.mp hh).2
  unfold Erdos66SaturatingCyclicFamily.actualMean at he
  have he' : ((Finset.univ.biUnion P).card:ℝ)*(Finset.univ.biUnion P).card/M ≤
      (1+η)*μ*(Fintype.card ι:ℝ)^2 := by nlinarith only [he]
  have he'' := (div_le_iff₀ hm).mp he'
  nlinarith only [he'']

/-- Logarithmically tuned disjoint palettes can be chosen with an arbitrarily
small fraction of the fine residues, in addition to all entrywise estimates. -/
theorem exists_sparse_disjoint_palette (c τ η ρ : ℝ)
    (hc : 0<c) (hτ : 0<τ) (hη : 0<η) (hρ : 0<ρ) (q N₀ : ℕ) :
    ∃ M : ℕ, N₀<M ∧ Odd M ∧ ∃ hM : NeZero M,
      ∃ μ : ℝ, 0<μ ∧ |μ/Real.log M-c|<τ ∧
        ∃ P : Fin q → Finset (ZMod M),
          Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
          ((Finset.univ.biUnion P).card:ℝ)/M<ρ ∧
          ∀ i j : Fin q, ∀ z : ZMod M,
            |(pairCount (P i) (P j) z:ℝ)-μ| ≤ η*μ := by
  have hlim : Tendsto
      (fun M : ℕ ↦ ((1+η)*(c+τ)*(q:ℝ)^2)*Real.log M/(M:ℝ)) atTop (𝓝 0) := by
    have hh := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul ((1+η)*(c+τ)*(q:ℝ)^2)
    simpa only [Function.comp_apply,id_eq,mul_zero,mul_div_assoc] using hh
  obtain ⟨L,hL⟩ := eventually_atTop.mp
    (hlim.eventually_lt_const (sq_pos_of_pos hρ))
  obtain ⟨M,hMN,hodd,hM,μ,hμ,htune,P,hP,hflat⟩ :=
    Erdos66NestedDifferencePalette.exists_logarithmic_disjoint_cyclic_palette
      c τ η hc hτ hη q (max N₀ (max L 2))
  letI := hM
  have hm : (0:ℝ)<M := by exact_mod_cast NeZero.pos M
  have hm1 : (1:ℝ)<M := by exact_mod_cast (show 1<M by omega)
  have hlog := Real.log_pos hm1
  have hμup : μ ≤ (c+τ)*Real.log M := by
    apply (div_le_iff₀ hlog).mp
    have hh := (abs_lt.mp htune).2
    linarith
  have hb : ((1+η)*(c+τ)*(q:ℝ)^2)*Real.log M < ρ^2*M :=
    (div_lt_iff₀ hm).mp (hL M (by omega))
  have hsc := palette_support_sq_bound M P hP μ η hflat
  simp only [Fintype.card_fin] at hsc
  have hu := mul_le_mul_of_nonneg_left hμup (show 0 ≤ (1+η)*(q:ℝ)^2 by positivity)
  have hub : (1+η)*μ*(q:ℝ)^2 < ρ^2*M := by nlinarith only [hu,hb]
  have hfinal := mul_lt_mul_of_pos_left hub hm
  have hs : ((Finset.univ.biUnion P).card:ℝ)<ρ*M := by
    apply (sq_lt_sq₀ (Nat.cast_nonneg _) (mul_pos hρ hm).le).mp
    nlinarith only [hsc,hfinal]
  exact ⟨M,by omega,hodd,hM,μ,hμ,htune,P,hP,(div_lt_iff₀ hm).mpr hs,hflat⟩

end Erdos66DisjointOperatorSupport

