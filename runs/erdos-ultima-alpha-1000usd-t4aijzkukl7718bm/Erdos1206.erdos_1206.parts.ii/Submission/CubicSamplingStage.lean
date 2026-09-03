import Submission.TrimmedSampling
import Submission.MaximumRootDeletion

/-! A simultaneous finite-prefix alteration lemma for the cubic hypergraph. -/
namespace Erdos1206.CubicSamplingStage
open Finset CubicHypergraph FiniteProductSampling PrefixSampling
open HypergraphHubTrimming TrimmedSampling MaximumRootDeletion
open scoped BigOperators Classical

noncomputable def sourcePrefix (S : Set ℕ) (N : ℕ) : Finset ℕ :=
  (range N).filter (fun n => n∈S)

lemma prefix_subset (S : Set ℕ) (N : ℕ) : sourcePrefix S N ⊆ range N := filter_subset _ _

lemma prefix_mono (S : Set ℕ) {N M : ℕ} (hNM : N ≤ M) : sourcePrefix S N ⊆ sourcePrefix S M := by
  intro v hv
  obtain ⟨hvN,hvS⟩ := mem_filter.mp hv
  exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hvN).trans_le hNM),hvS⟩

lemma chosen_prefix {S : Set ℕ} {M N k : ℕ} [NeZero k] (hNM : N ≤ M)
    (ω : Fin M → Fin k) :
    (chosen ω (sourcePrefix S M)).filter (fun v => v < N)=chosen ω (sourcePrefix S N) := by
  ext v
  simp only [chosen,sourcePrefix,mem_filter,mem_range]
  constructor
  · rintro ⟨⟨⟨_,hS⟩,hω⟩,hN⟩
    exact ⟨⟨hN,hS⟩,hω⟩
  · rintro ⟨⟨hN,hS⟩,hω⟩
    exact ⟨⟨⟨hN.trans_le hNM,hS⟩,hω⟩,hN⟩

lemma edges_chosen {S : Set ℕ} {M N k : ℕ} [NeZero k] (hNM : N ≤ M)
    (ω : Fin M → Fin k) :
    edges N (chosen ω (sourcePrefix S M))=full (edges N S) ω := by
  ext e
  simp only [mem_edges,full,mem_filter]
  constructor
  · rintro ⟨hN,hS,hE⟩
    refine ⟨⟨hN,?_,hE⟩,?_⟩
    · intro v hv
      have hh := hS hv
      simp only [chosen,sourcePrefix,mem_coe,mem_filter] at hh
      exact hh.1.2
    · intro v hv
      have hh := hS hv
      change v∈(sourcePrefix S M).filter (fun v => label ω v=0) at hh
      exact (mem_filter.mp hh).2
  · rintro ⟨⟨hN,hS,hE⟩,hω⟩
    refine ⟨hN,?_,hE⟩
    intro v hv
    exact mem_filter.mpr ⟨mem_filter.mpr
      ⟨mem_range.mpr ((mem_range.mp (hN hv)).trans_le hNM),hS hv⟩,hω v hv⟩

/-- Explicit moment-budget criterion for one finite Sidon witness meeting
all the requested prefix lower bounds. -/
theorem finite_stage_in_source (S : Set ℕ) (T : Finset ℕ) (N D : ℕ → ℕ)
    {M k : ℕ} [NeZero k] {ε : ℝ} (hε : 0 < ε)
    (hNM : ∀ j∈T, N j ≤ M) (hN : ∀ j∈T, 0 < N j)
    (hsource : ∀ j∈T, 8*ε*(k:ℝ)*N j ≤ (sourcePrefix S (N j)).card)
    (hmean : ∀ j∈T, ((edges (N j) S).card:ℝ)/(k:ℝ)^3 ≤ ε*N j)
    (hbad : ∀ j∈T, ((bad (edges (N j) S) (hubs (edges (N j) S) (D j))).card:ℝ) ≤ ε*N j)
    (hcost : ∑ j∈T, ((N j:ℝ)+4*(edges (N j) S).card*D j)/(ε*N j)^2 < 1) :
    ∃ B : Finset ℕ, B ⊆ sourcePrefix S M ∧
      IsSidon ((fun n : ℕ => n^3) '' (B : Set ℕ)) ∧
      ∀ j∈T, 4*ε*N j ≤ ((B.filter (fun v => v < N j)).card:ℝ) := by
  have hkR : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  let E := fun j => edges (N j) S
  let H := fun j => hubs (E j) (D j)
  let X := fun j (ω : Fin M → Fin k) => ((chosen ω (sourcePrefix S (N j))).card:ℝ)
  let μ := fun j => ((sourcePrefix S (N j)).card:ℝ)/(k:ℝ)
  let Y := fun j (ω : Fin M → Fin k) => score (E j) (H j) ω
  let ν := fun j => (𝔼 ω : Fin M → Fin k, Y j ω)
  let f := fun j ω => (X j ω-μ j)/(ε*N j)
  let g := fun j ω => (Y j ω-ν j)/(ε*N j)
  let c := fun j => ((N j:ℝ)+4*(E j).card*D j)/(ε*N j)^2
  have hvar (j : ℕ) (hj : j∈T) :
      (𝔼 ω : Fin M → Fin k, (f j ω)^2)+(𝔼 ω : Fin M → Fin k, (g j ω)^2) ≤ c j := by
    have hpre := (prefix_subset S (N j)).trans (range_mono (hNM j hj))
    have hX := chosen_variance (k := k) hpre
    have hY := score_variance (E j) (D j) (M := M) (k := k)
      (fun e he => (mem_edges.mp he).2.2.card)
    have hc : ((sourcePrefix S (N j)).card:ℝ) ≤ N j := by
      exact_mod_cast (card_le_card (prefix_subset S (N j))).trans_eq (card_range (N j))
    dsimp only [f,g,c]
    simp_rw [div_pow,←expect_div]
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    change (𝔼 ω : Fin M → Fin k, (X j ω-μ j)^2) ≤ _ at hX
    change (𝔼 ω : Fin M → Fin k, (Y j ω-ν j)^2) ≤ _ at hY
    linarith
  obtain ⟨ω,hω⟩ := SamplingVariance.exists_simultaneous_two_bands T f g c hvar hcost
  let P := chosen ω (sourcePrefix S M)
  let B := keep P (edges M P)
  have hPM : P ⊆ range M := (filter_subset _ _).trans (prefix_subset S M)
  refine ⟨B,sdiff_subset.trans (filter_subset _ _),cubeSidon_keep hPM,?_⟩
  intro j hj
  have hden : 0 < ε*(N j:ℝ) := mul_pos hε (by exact_mod_cast hN j hj)
  have hXdev : |X j ω-μ j| < ε*N j := by
    have hh := (hω j hj).1
    dsimp only [f] at hh
    rwa [abs_div,abs_of_pos hden,div_lt_one hden] at hh
  have hYdev : |Y j ω-ν j| < ε*N j := by
    have hh := (hω j hj).2
    dsimp only [g] at hh
    rwa [abs_div,abs_of_pos hden,div_lt_one hden] at hh
  have hμ : 8*ε*N j ≤ μ j := by
    dsimp only [μ]
    apply (le_div_iff₀ hkR).mpr
    nlinarith only [hsource j hj]
  have hν : ν j ≤ ε*N j := by
    apply le_trans (score_mean_le (E j) (H j)
      (fun e he => (mem_edges.mp he).1.trans (range_mono (hNM j hj)))
      (fun e he => (mem_edges.mp he).2.2.card))
    exact hmean j hj
  have hfull : ((full (E j) ω).card:ℝ) ≤ Y j ω+ε*N j :=
    (full_card_le (E j) (H j) ω
      (fun e he => (mem_edges.mp he).1.trans (range_mono (hNM j hj)))).trans
      (add_le_add_right (hbad j hj) _)
  have hloss := cubic_prefix_bound hPM (N j)
  rw [chosen_prefix (hNM j hj) ω,edges_chosen (hNM j hj) ω] at hloss
  have hlossR : X j ω ≤ ((B.filter (fun v => v < N j)).card:ℝ)+(full (E j) ω).card := by
    dsimp only [X,B,E]
    exact_mod_cast hloss
  have hxlo := (abs_lt.mp hXdev).1
  have hyhi := (abs_lt.mp hYdev).2
  linarith

/-- The original range-only interface, obtained from the stronger source
containment conclusion. -/
theorem finite_stage (S : Set ℕ) (T : Finset ℕ) (N D : ℕ → ℕ)
    {M k : ℕ} [NeZero k] {ε : ℝ} (hε : 0 < ε)
    (hNM : ∀ j∈T, N j ≤ M) (hN : ∀ j∈T, 0 < N j)
    (hsource : ∀ j∈T, 8*ε*(k:ℝ)*N j ≤ (sourcePrefix S (N j)).card)
    (hmean : ∀ j∈T, ((edges (N j) S).card:ℝ)/(k:ℝ)^3 ≤ ε*N j)
    (hbad : ∀ j∈T, ((bad (edges (N j) S) (hubs (edges (N j) S) (D j))).card:ℝ) ≤ ε*N j)
    (hcost : ∑ j∈T, ((N j:ℝ)+4*(edges (N j) S).card*D j)/(ε*N j)^2 < 1) :
    ∃ B : Finset ℕ, B ⊆ range M ∧
      IsSidon ((fun n : ℕ => n^3) '' (B : Set ℕ)) ∧
      ∀ j∈T, 4*ε*N j ≤ ((B.filter (fun v => v < N j)).card:ℝ) := by
  obtain ⟨B,hB,hSidon,hgrid⟩ := finite_stage_in_source S T N D hε hNM hN
    hsource hmean hbad hcost
  exact ⟨B,hB.trans (prefix_subset S M),hSidon,hgrid⟩

#print axioms finite_stage_in_source
#print axioms finite_stage
end Erdos1206.CubicSamplingStage
