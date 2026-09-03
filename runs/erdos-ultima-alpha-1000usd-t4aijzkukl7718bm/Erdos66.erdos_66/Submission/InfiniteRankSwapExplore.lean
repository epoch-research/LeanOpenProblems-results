import Submission.GlobalRankPacketRepairExplore

/-! Passing rank-assigned finite swaps to an infinite bijective replacement.
The explicit location bound supplies the required finite-prefix truncation. -/
namespace Erdos66InfiniteRankSwap
open Erdos66Counting Erdos66Fractional Erdos66ClampedPrefixContinuation
  Erdos66RankProfileGap Erdos66BracketRankMove Erdos66RankCellExchange
  Erdos66GlobalRankPacketRepair Erdos66OrderedPartialReplacement Erdos66Generating
open scoped Classical
set_option maxHeartbeats 3200000

 theorem infinite_rank_swap_brackets (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (D F : Set ℕ) (hFA : Disjoint F A)
    (himage : (fun u ↦ rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)) '' F=D)
    (hinj : Set.InjOn (fun u ↦ rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)) F)
    (hloc : ∀ u∈F, u ≤ 2*rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)) :
    ∀ L, PrefixBrackets profile ((A\D)∪F) L := by
  let assign (u : ℕ) := rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)
  intro L
  let F₀ := cutoff F (2*L+1)
  let D₀ := F₀.image assign
  have hF₀ : Disjoint (F₀ : Set ℕ) A := Set.disjoint_left.mpr
    (fun u hu huA ↦ Set.disjoint_left.mp hFA (mem_cutoff.mp hu).2 huA)
  have hbr₀ := rank_assigned_swap_brackets A hbr D₀ F₀ hF₀ rfl (by
    intro u hu v hv he
    exact hinj (mem_cutoff.mp hu).2 (mem_cutoff.mp hv).2 he)
  have hDmem (i : ℕ) (hi : i<L) : i∈D₀ ↔ i∈D := by
    constructor
    · intro hiD
      obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hiD
      rw [←himage]
      exact ⟨u,(mem_cutoff.mp hu).2,he⟩
    · intro hiD
      rw [←himage] at hiD
      obtain ⟨u,hu,he⟩ := hiD
      have hb := hloc u hu
      dsimp only at he
      rw [he] at hb
      exact Finset.mem_image.mpr ⟨u,mem_cutoff.mpr ⟨by omega,hu⟩,he⟩
  have hFmem (i : ℕ) (hi : i<L) : i∈F₀ ↔ i∈F := by
    simp only [F₀,mem_cutoff,show i<2*L+1 by omega,true_and]
  have heq (i : ℕ) (hi : i<L) : i∈swap A D₀ F₀ ↔ i∈(A\D)∪F := by
    simp only [swap,Set.mem_union,Set.mem_diff,Finset.mem_coe,hDmem i hi,hFmem i hi]
  intro k hk
  have he : mass (indicator (swap A D₀ F₀)) k=mass (indicator ((A\D)∪F)) k := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    by_cases hu : i∈(A\D)∪F <;> simp [indicator,heq i (by omega),hu]
  rw [←he]
  exact hbr₀ L k hk

end Erdos66InfiniteRankSwap
