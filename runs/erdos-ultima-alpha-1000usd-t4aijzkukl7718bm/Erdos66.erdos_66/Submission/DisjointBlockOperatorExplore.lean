import Submission.NestedDifferencePaletteExplore
import Submission.ColoredBlockTransferExplore

/-! A fixed disjoint cyclic palette yields one natural-number operator for
all later infinite coarse color sets. The old carry formula is used exactly. -/
namespace Erdos66DisjointBlockOperator
open Erdos66OriginRepair Erdos66DisjointPaletteAssembly
  Erdos66NestedDifferencePalette Erdos66OuterCarryProfile
  Erdos66ColoredBlockTransfer Erdos66IntegerBlock Erdos66CyclicThickening
  AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 2600000

variable {G ι : Type*} [AddCommGroup G] [DecidableEq G]
  [Fintype ι] [DecidableEq ι]

lemma selected_union_count (P : ι → Finset G)
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (S T : Finset ι) (z : G) :
    pairCount (S.biUnion P) (T.biUnion P) z =
      ∑ i∈S, ∑ j∈T, pairCount (P i) (P j) z := by
  rw [pairCount_biUnion_left S P (fun i hi j hj hij ↦ hP hij)]
  simp_rw [pairCount_biUnion_right T P (fun i hi j hj hij ↦ hP hij)]

lemma selected_union_error (P : ι → Finset G)
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (S T : Finset ι) (z : G) (μ E : ℝ)
    (hflat : ∀ i∈S, ∀ j∈T, |(pairCount (P i) (P j) z:ℝ)-μ| ≤ E) :
    |(pairCount (S.biUnion P) (T.biUnion P) z:ℝ)-μ*S.card*T.card| ≤ E*S.card*T.card := by
  rw [selected_union_count P hP]
  push_cast
  have hmain : (∑ i∈S, ∑ j∈T, (μ:ℝ))=μ*S.card*T.card := by simp; ring
  have herr : (∑ i∈S, ∑ j∈T, (E:ℝ))=E*S.card*T.card := by simp; ring
  rw [←hmain,←herr]
  simp_rw [←Finset.sum_sub_distrib]
  exact ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun i hi ↦ Finset.abs_sum_le_sum_abs _ _))).trans
    (Finset.sum_le_sum (fun i hi ↦ Finset.sum_le_sum (fun j hj ↦ hflat i hi j hj)))

noncomputable def active (B : ι → Set ℕ) (n : ℕ) : Finset ι :=
  Finset.univ.filter (fun i ↦ n ∈ B i)

noncomputable def colorWeight (B : ι → Set ℕ) (n : ℕ) : ℝ := (active B n).card

noncomputable def colorBlocks (P : ι → Finset G) (B : ι → Set ℕ) (n : ℕ) : Finset G :=
  (active B n).biUnion P

lemma colorWeight_bounds (B : ι → Set ℕ) (n : ℕ) :
    0 ≤ colorWeight B n ∧ colorWeight B n ≤ Fintype.card ι := by
  constructor
  · exact Nat.cast_nonneg _
  · dsimp only [colorWeight]
    exact_mod_cast Finset.card_le_univ (active B n)

lemma colorBlocks_mixed_error (P : ι → Finset G)
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (μ η : ℝ) (hflat : ∀ i j z, |(pairCount (P i) (P j) z:ℝ)-μ| ≤ η*μ)
    (B C : ι → Set ℕ) (n m : ℕ) (z : G) :
    |(pairCount (colorBlocks P B n) (colorBlocks P C m) z:ℝ)-
      μ*colorWeight B n*colorWeight C m| ≤ η*(μ*colorWeight B n*colorWeight C m) := by
  have he := selected_union_error P hP (active B n) (active C m) z μ (η*μ)
    (fun i hi j hj ↦ hflat i j z)
  change |(pairCount (colorBlocks P B n) (colorBlocks P C m) z:ℝ)-
      μ*colorWeight B n*colorWeight C m| ≤ (η*μ)*colorWeight B n*colorWeight C m at he
  convert he using 1 <;> ring

variable (M : ℕ) [NeZero M]

noncomputable def naturalOperator (K : ℕ) [NeZero K]
    (P : ι → Finset (ZMod M)) (B : ι → Set ℕ) : Set ℕ :=
  blockSet (M*K) (fun n ↦ outerLift M K (colorBlocks P B n))

/-- Exact membership in the actual natural-number output. -/
lemma naturalOperator_mem (K : ℕ) [NeZero K]
    (P : ι → Finset (ZMod M)) (B : ι → Set ℕ) (a : ℕ) :
    a ∈ naturalOperator M K P B ↔
      ∃ i, a/(M*K) ∈ B i ∧ reduceDigit M K (a : ZMod (M*K)) ∈ P i := by
  simp only [naturalOperator,blockSet,Set.mem_setOf_eq,mem_outerLift,
    colorBlocks,Finset.mem_biUnion,active,Finset.mem_filter,Finset.mem_univ,true_and]

/-- Agreement of coarse prefixes gives agreement of the corresponding
natural prefixes. This keeps M, K, and P fixed. -/
lemma naturalOperator_prefix_congr (K : ℕ) [NeZero K]
    (P : ι → Finset (ZMod M)) (B C : ι → Set ℕ) (N : ℕ)
    (hBC : ∀ i k, k ≤ N → (k ∈ B i ↔ k ∈ C i))
    (a : ℕ) (ha : a<(N+1)*(M*K)) :
    a ∈ naturalOperator M K P B ↔ a ∈ naturalOperator M K P C := by
  have hdiv : a/(M*K)<N+1 :=
    (Nat.div_lt_iff_lt_mul (Nat.mul_pos (NeZero.pos M) (NeZero.pos K))).mpr ha
  simp only [naturalOperator_mem]
  exact exists_congr (fun i ↦ and_congr_left (fun _ ↦ hBC i _ (by omega)))

/-- Actual natural-number counts, including both carry terms. The input
color sets may be infinite and may overlap arbitrarily. -/
theorem natural_operator_profile_error (K : ℕ) [NeZero K]
    (P : ι → Finset (ZMod M))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (μ η : ℝ) (hμ : 0 ≤ μ) (hη : 0 ≤ η)
    (hflat : ∀ i j z, |(cyclicCount M (P i) (P j) z:ℝ)-μ| ≤ η*μ)
    (B : ι → Set ℕ) (n : ℕ) (hn : 0<n) (t : ZMod M) (r : Fin K) :
    |(sumRep (naturalOperator M K P B) (n*(M*K)+(blockDigit M K t r).val):ℝ)-
      μ*(r.val*profileConv (colorWeight B) n+
        ((K:ℝ)-r.val)*profileConv (colorWeight B) (n-1))| ≤
      μ*(K*η+1+η)*(profileConv (colorWeight B) n+profileConv (colorWeight B) (n-1)) := by
  exact colored_block_profile_error M K (colorBlocks P B) (colorWeight B) μ η hμ hη
    (fun n ↦ (colorWeight_bounds B n).1)
    (fun i j z ↦ colorBlocks_mixed_error P hP μ η hflat B B i j z) n hn t r

/-- The fine modulus and palette precede ALL infinite coarse inputs, ALL
outer repetition counts, and ALL targets in the displayed range. -/
theorem exists_universal_natural_operator (c τ η : ℝ)
    (hc : 0<c) (hτ : 0<τ) (hη : 0<η) (q N₀ : ℕ) :
    ∃ M : ℕ, N₀<M ∧ Odd M ∧ ∃ hM : NeZero M,
      ∃ μ : ℝ, 0<μ ∧ |μ/Real.log M-c|<τ ∧
        ∃ P : Fin q → Finset (ZMod M),
          Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
          ∀ K : ℕ, ∀ hK : NeZero K, ∀ (B : Fin q → Set ℕ)
            (n : ℕ), 0<n → ∀ (t : ZMod M) (r : Fin K),
            |(sumRep (naturalOperator M K P B) (n*(M*K)+(blockDigit M K t r).val):ℝ)-
              μ*(r.val*profileConv (colorWeight B) n+
                ((K:ℝ)-r.val)*profileConv (colorWeight B) (n-1))| ≤
              μ*(K*η+1+η)*
                (profileConv (colorWeight B) n+profileConv (colorWeight B) (n-1)) := by
  obtain ⟨M,hMN,hodd,hM,μ,hμ,htune,P,hP,hflat⟩ :=
    exists_logarithmic_disjoint_cyclic_palette c τ η hc hτ hη q N₀
  letI := hM
  refine ⟨M,hMN,hodd,hM,μ,hμ,htune,P,hP,fun K hK B n hn t r ↦ ?_⟩
  letI := hK
  exact natural_operator_profile_error M K P hP μ η hμ.le hη.le hflat B n hn t r

end Erdos66DisjointBlockOperator
