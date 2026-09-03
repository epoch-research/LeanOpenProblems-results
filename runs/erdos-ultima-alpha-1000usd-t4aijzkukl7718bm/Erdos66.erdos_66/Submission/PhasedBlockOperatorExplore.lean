import Submission.DisjointBlockOperatorExplore
import Submission.TranslatedPrefixPaletteExplore

/-! Arbitrary block phases in the fixed-palette natural-number operator.
The two integer carry contributions remain explicit. -/
namespace Erdos66PhasedBlockOperator
open AdditiveCombinatorics Erdos66DisjointBlockOperator
  Erdos66TranslatedPrefixPalette Erdos66ColoredBlockTransfer
  Erdos66IntegerBlock Erdos66OuterCarryProfile Erdos66CyclicThickening
  Erdos66NestedDifferencePalette
open scoped Classical
set_option maxHeartbeats 1600000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (M : ℕ) [NeZero M]

noncomputable def phasedBlocks (P : ι → Finset (ZMod M))
    (B : ι → Set ℕ) (s : ℕ → ZMod M) (n : ℕ) : Finset (ZMod M) :=
  shift M (colorBlocks P B n) (s n)

lemma phasedBlocks_mixed_error (P : ι → Finset (ZMod M))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j))) (μ η : ℝ)
    (hflat : ∀ i j z, |(cyclicCount M (P i) (P j) z:ℝ)-μ| ≤ η*μ)
    (B C : ι → Set ℕ) (s t : ℕ → ZMod M) (n m : ℕ) (z : ZMod M) :
    |(cyclicCount M (phasedBlocks M P B s n) (phasedBlocks M P C t m) z:ℝ)-
      μ*colorWeight B n*colorWeight C m| ≤ η*(μ*colorWeight B n*colorWeight C m) := by
  rw [phasedBlocks, phasedBlocks, shift_cyclicCount]
  exact colorBlocks_mixed_error P hP μ η hflat B C n m (z-s n-t m)

noncomputable def phasedOperator (K : ℕ) [NeZero K]
    (P : ι → Finset (ZMod M)) (B : ι → Set ℕ) (s : ℕ → ZMod M) : Set ℕ :=
  blockSet (M*K) (fun n ↦ outerLift M K (phasedBlocks M P B s n))

lemma phasedOperator_mem (K : ℕ) [NeZero K]
    (P : ι → Finset (ZMod M)) (B : ι → Set ℕ) (s : ℕ → ZMod M) (a : ℕ) :
    a ∈ phasedOperator M K P B s ↔
      ∃ i, a/(M*K) ∈ B i ∧
        reduceDigit M K (a : ZMod (M*K))-s (a/(M*K)) ∈ P i := by
  simp only [phasedOperator,blockSet,Set.mem_setOf_eq,mem_outerLift,
    phasedBlocks,mem_shift,colorBlocks,Finset.mem_biUnion,
    active,Finset.mem_filter,Finset.mem_univ,true_and]

lemma phasedOperator_prefix_congr (K : ℕ) [NeZero K]
    (P : ι → Finset (ZMod M)) (B C : ι → Set ℕ) (s t : ℕ → ZMod M) (N : ℕ)
    (hBC : ∀ i k, k ≤ N → (k ∈ B i ↔ k ∈ C i))
    (hst : ∀ k ≤ N, s k=t k) (a : ℕ) (ha : a<(N+1)*(M*K)) :
    a ∈ phasedOperator M K P B s ↔ a ∈ phasedOperator M K P C t := by
  have hdiv : a/(M*K)<N+1 :=
    (Nat.div_lt_iff_lt_mul (Nat.mul_pos (NeZero.pos M) (NeZero.pos K))).mpr ha
  simp only [phasedOperator_mem,hst _ (by omega : a/(M*K) ≤ N)]
  exact exists_congr (fun i ↦ and_congr_left (fun _ ↦ hBC i _ (by omega)))

/-- Phases can vary at every coarse block, without increasing the old error. -/
theorem phased_operator_profile_error (K : ℕ) [NeZero K]
    (P : ι → Finset (ZMod M))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (μ η : ℝ) (hμ : 0 ≤ μ) (hη : 0 ≤ η)
    (hflat : ∀ i j z, |(cyclicCount M (P i) (P j) z:ℝ)-μ| ≤ η*μ)
    (B : ι → Set ℕ) (s : ℕ → ZMod M) (n : ℕ) (hn : 0<n)
    (t : ZMod M) (r : Fin K) :
    |(sumRep (phasedOperator M K P B s) (n*(M*K)+(blockDigit M K t r).val):ℝ)-
      μ*(r.val*profileConv (colorWeight B) n+
        ((K:ℝ)-r.val)*profileConv (colorWeight B) (n-1))| ≤
      μ*(K*η+1+η)*(profileConv (colorWeight B) n+profileConv (colorWeight B) (n-1)) := by
  exact colored_block_profile_error M K (phasedBlocks M P B s) (colorWeight B) μ η hμ hη
    (fun n ↦ (colorWeight_bounds B n).1)
    (fun i j z ↦ phasedBlocks_mixed_error M P hP μ η hflat B B s s i j z) n hn t r

/-- The same palette works for every later infinite coarse input and phase sequence. -/
theorem exists_universal_phased_operator (c τ η : ℝ)
    (hc : 0<c) (hτ : 0<τ) (hη : 0<η) (q N₀ : ℕ) :
    ∃ M : ℕ, N₀<M ∧ Odd M ∧ ∃ hM : NeZero M,
      ∃ μ : ℝ, 0<μ ∧ |μ/Real.log M-c|<τ ∧
        ∃ P : Fin q → Finset (ZMod M),
          Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
          ∀ K : ℕ, ∀ hK : NeZero K, ∀ (B : Fin q → Set ℕ)
            (s : ℕ → ZMod M) (n : ℕ), 0<n → ∀ (t : ZMod M) (r : Fin K),
            |(sumRep (phasedOperator M K P B s) (n*(M*K)+(blockDigit M K t r).val):ℝ)-
              μ*(r.val*profileConv (colorWeight B) n+
                ((K:ℝ)-r.val)*profileConv (colorWeight B) (n-1))| ≤
              μ*(K*η+1+η)*
                (profileConv (colorWeight B) n+profileConv (colorWeight B) (n-1)) := by
  obtain ⟨M,hMN,hodd,hM,μ,hμ,htune,P,hP,hflat⟩ :=
    exists_logarithmic_disjoint_cyclic_palette c τ η hc hτ hη q N₀
  letI := hM
  refine ⟨M,hMN,hodd,hM,μ,hμ,htune,P,hP,fun K hK B s n hn t r ↦ ?_⟩
  letI := hK
  exact phased_operator_profile_error M K P hP μ η hμ.le hη.le hflat B s n hn t r

end Erdos66PhasedBlockOperator
