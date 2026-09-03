import Submission.AdaptiveSingletonSelectionExplore
import Submission.GlobalRankPacketRepairExplore
import Submission.RankCellWindowExplore

/-! Restoring original rank cells with one common insertion-load potential.
No central partner hypothesis is imposed on the prescribed deletion set. -/
namespace Erdos66RankRestorationSelection
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66FiniteSwapAlgebra
  Erdos66AdaptiveSingletonAlgebra Erdos66AdaptiveSingletonSelection
  Erdos66Counting Erdos66OrderedPartialReplacement Erdos66Fractional
  Erdos66ClampedPrefixContinuation Erdos66BracketRankMove Erdos66RankCellExchange
  Erdos66RankProfileGap Erdos66GlobalRankPacketRepair
open scoped Classical
set_option maxHeartbeats 3000000

theorem exists_rank_restoration {α : Type*} [Fintype α]
    (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L) (A₀ D : Finset ℕ)
    (n m : ℕ) (d : ℕ → ℕ) (f : ℕ → α → ℕ)
    (himage : (Finset.range m).image d=D) (hdinj : Set.InjOn d (Finset.range m : Set ℕ))
    (hinj : ∀ k < m, Function.Injective (f k)) (hhalf : ∀ k < m, ∀ a, n<2*f k a)
    (hrank : ∀ k < m, ∀ a,
      rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile (f k a))=d k)
    (hcut : ∀ k < m, ∀ a, f k a∈A ↔ f k a∈A₀)
    (B₀ B₁ : ℝ)
    (hB₀ : ∀ k < m, ((Finset.univ.filter (fun a ↦ f k a∈A₀)).card : ℝ) ≤ B₀)
    (hB₁ : ∀ k < m, ((partnerChoices A₀ (f k) n).card : ℝ) ≤ B₁)
    (T : Finset ℕ) (q t : ℝ) (K R : ℕ → ℝ) (hq : 0<q) (ht : 0<t)
    (hK : ∀ k < m, ∀ z∈T, ((partnerChoices A₀ (f k) z).card : ℝ) ≤ K z)
    (hbudget : q+B₀+B₁ ≤ Fintype.card α)
    (hsmall : (∑ z∈T, Real.exp ((m : ℝ)*(Real.exp t*(K z+m+1)/q)-t*R z))<1) :
    ∃ F : Finset ℕ, F.card=D.card ∧ Disjoint A₀ F ∧ Disjoint (F : Set ℕ) A ∧
      (∀ u∈F, ∃ k < m, ∃ a, u=f k a) ∧
      (∀ L, PrefixBrackets profile (swap A D F) L) ∧
      ∀ z∈T, insertionEnergy A₀ F z < 5*R z := by
  let assign := fun u ↦ rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)
  have hrows : ∀ i < m, ∀ j < m, i≠j → ∀ a b, f i a≠f j b := by
    intro i hi j hj hij a b he
    have hh := congrArg assign he
    change rankPoint A _ (cell profile (f i a))=rankPoint A _ (cell profile (f j b)) at hh
    rw [hrank i hi a,hrank j hj b] at hh
    exact hij (hdinj (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) hh)
  have hDc : D.card=m := by
    rw [←himage,Finset.card_image_of_injOn hdinj,Finset.card_range]
  obtain ⟨F,hFc,hF,hpoints,hcover,_hFA,_hFF,hload⟩ := exists_adaptive_singletons A₀ n m f
    hinj hrows hhalf B₀ B₁ hB₀ hB₁ T q t K R hq ht hK hbudget hsmall
  have hFA' : Disjoint (F : Set ℕ) A := by
    apply Set.disjoint_left.mpr
    intro u hu hua
    obtain ⟨k,hk,a,rfl⟩ := hpoints u hu
    exact Finset.disjoint_left.mp hF ((hcut k hk a).mp hua) hu
  have hshape : F.image assign=D := by
    apply Finset.Subset.antisymm
    · intro u hu
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨k,hk,a,rfl⟩ := hpoints v hv
      change rankPoint A _ (cell profile (f k a))∈D
      rw [hrank k hk a,←himage]
      exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr hk,rfl⟩
    · intro u hu
      rw [←himage] at hu
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨a,ha⟩ := hcover k (Finset.mem_range.mp hk)
      exact Finset.mem_image.mpr ⟨f k a,ha,hrank k (Finset.mem_range.mp hk) a⟩
  have hiF : Set.InjOn assign (F : Set ℕ) := Finset.card_image_iff.mp (by rw [hshape,hDc,hFc])
  exact ⟨F,hFc.trans hDc.symm,hF,hFA',hpoints,
    rank_assigned_swap_brackets A hbr D F hFA' hshape.symm hiF,hload⟩

end Erdos66RankRestorationSelection
