import Submission.UniversalBernsteinGraphExplore
import Submission.UniversalCompleteNaturalExplore

/-! Universal Bernstein colors for actual mixed sets and the ordinary
natural-number carry operator. All coarse profiles remain explicit inputs. -/
namespace Erdos66UniversalBernsteinActual
open Erdos66UniformColorMoments Erdos66CompleteKernelBasis
  Erdos66UniversalBernsteinGraph Erdos66UniversalCompleteGraph
  Erdos66UniversalCompleteCyclic Erdos66UniversalCompleteNatural
  Erdos66UniformGraphColorTransfer Erdos66TranslatedGraphPartition
  Erdos66OriginRepair Erdos66MixedDisjointAssembly
  Erdos66InfiniteKernelLocality Erdos66InfiniteMixedKernel
  Erdos66OuterCarryProfile Erdos66DisjointBlockOperator Erdos66ColoredBlockTransfer Erdos66CyclicThickening
  AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 3000000
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {H : Type*} [AddCommGroup H] [DecidableEq H]

/-- Both finite coarse families and every target are chosen after the same
coloring; overlaps between and within the families are permitted. -/
theorem exists_universal_bernstein_actual_mixed {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2) :
    ∃ ω : Fin n → α, ∀ (f : F → F) (D : ℕ), HasBoundedSums f D →
      ∀ ε : ℝ, 0≤ε → (D:ℝ)^2*paletteCost n (Fintype.card α)≤ε^2*(n:ℝ)^2 →
      ∀ (B C : α → Finset H) (q : H) (t s : F),
        |(pairCount (graphSet f ρ B ω) (graphSet f ρ C ω) ((t,s),q):ℝ)-
          (n:ℝ)^2*kernelMean (mixedKernel B C q)|≤
            ε*(n:ℝ)^2*kernelMean (mixedKernel B C q) := by
  obtain ⟨ω,hω⟩ := exists_universal_bernstein_graph_accuracy (α := α) ρ hF
  refine ⟨ω,fun f D hf ε hε hsize B C q t s ↦ ?_⟩
  rw [graphSet_mixed_pairCount]
  exact hω f D hf ε hε hsize (mixedKernel B C q) (fun _ _ ↦ Nat.cast_nonneg _) t s

/-- Genuine infinite coarse sets, without a support cutoff or finite list. -/
theorem exists_universal_bernstein_infinite_mixed {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2) :
    ∃ ω : Fin n → α, ∀ (f : F → F) (D : ℕ), HasBoundedSums f D →
      ∀ ε : ℝ, 0≤ε → (D:ℝ)^2*paletteCost n (Fintype.card α)≤ε^2*(n:ℝ)^2 →
      ∀ (B C : α → Set ℕ) (q : ℕ) (t s : F),
        |(setPairCount (infiniteGraphSet f ρ B ω) (infiniteGraphSet f ρ C ω) ((t,s),(q:ℤ)):ℝ)-
          (n:ℝ)^2*kernelMean (infiniteMixedKernel B C q)|≤
            ε*(n:ℝ)^2*kernelMean (infiniteMixedKernel B C q) := by
  obtain ⟨ω,hω⟩ := exists_universal_bernstein_graph_accuracy (α := α) ρ hF
  refine ⟨ω,fun f D hf ε hε hsize B C q t s ↦ ?_⟩
  rw [infinite_graph_mixed_identity]
  exact hω f D hf ε hε hsize (infiniteMixedKernel B C q) (infiniteMixedKernel_nonneg B C q) t s

/-- Actual complete disjoint plane colors with the improved alphabet cost. -/
theorem exists_bernstein_plane_colors {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2) :
    ∃ ω : Fin n → α, ∀ (f : F → F) (D : ℕ), HasBoundedSums f D →
      ∀ ε : ℝ, 0≤ε → (D:ℝ)^2*paletteCost n (Fintype.card α)≤ε^2*(n:ℝ)^2 →
      ∀ a b : α, ∀ t s : F,
        |(pairCount (colorClass f ρ ω a) (colorClass f ρ ω b) (t,s):ℝ)-
          (n:ℝ)^2/(Fintype.card α:ℝ)^2|≤ε*((n:ℝ)^2/(Fintype.card α:ℝ)^2) := by
  obtain ⟨ω,hω⟩ := exists_universal_bernstein_graph_accuracy (α := α) ρ hF
  refine ⟨ω,fun f D hf ε hε hsize a b t s ↦ ?_⟩
  have he := hω f D hf ε hε hsize (mask (a,b)) (mask_nonneg (a,b)) t s
  rw [←colorClass_pairCount,mask_mean] at he
  simpa only [Fintype.card_prod,Nat.cast_mul,div_eq_mul_inv,pow_two,mul_one,one_mul,mul_assoc] using he

variable {p : ℕ} [Fact p.Prime]

/-- Both carry levels are retained. The coloring precedes every later
thickening, outer repetition count, graph, and infinite coarse family. This
is a fixed-field operator, not a compatible changing-field construction. -/
theorem exists_universal_bernstein_natural (ρ : Fin p ≃ ZMod p) (hp : p≠2) :
    ∃ ω : Fin p → α, ∀ (K L : ℕ), ∀ _hK : NeZero K, ∀ _hL : NeZero L,
      ∀ (f : ZMod p → ZMod p) (D : ℕ), HasBoundedSums f D →
      ∀ ε : ℝ, 0≤ε → (D:ℝ)^2*paletteCost p (Fintype.card α)≤ε^2*(p:ℝ)^2 →
      ∀ (B : α → Set ℕ) (n : ℕ), 0<n →
      ∀ (z : ZMod ((p*K)^2)) (r : Fin L),
        |(sumRep (naturalSet p K L f ρ ω B)
            (n*(((p*K)^2)*L)+(blockDigit ((p*K)^2) L z r).val):ℝ)-
          cyclicMean (α := α) p K*(r.val*profileConv (colorWeight B) n+
            ((L:ℝ)-r.val)*profileConv (colorWeight B) (n-1))|≤
          cyclicMean (α := α) p K*(L*carryRelative K ε+1+carryRelative K ε)*
            (profileConv (colorWeight B) n+profileConv (colorWeight B) (n-1)) := by
  obtain ⟨ω,hω⟩ := exists_bernstein_plane_colors (α := α) ρ
    (by simpa only [ZMod.ringChar_zmod_n] using hp)
  refine ⟨ω,fun K L hK hL f D hf ε hε hsize B n hn z r ↦ ?_⟩
  letI := hK
  letI := hL
  exact naturalSet_profile_error p K L f ρ ω ε hε
    (hω f D hf ε hε hsize) B n hn z r

end Erdos66UniversalBernsteinActual
