import Submission.AdaptiveSingletonSelectionExplore
import Submission.GlobalRankPacketRepairExplore
import Submission.RankCellWindowExplore

/-! Count-preserving downward relocation of prescribed old endpoints.
The deletion loss at other targets remains explicit. -/
namespace Erdos66PrescribedRankRelocation
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66FiniteSwapAlgebra
  Erdos66AdaptiveSingletonAlgebra Erdos66AdaptiveSingletonSelection
  Erdos66Counting Erdos66OrderedPartialReplacement Erdos66Fractional
  Erdos66ClampedPrefixContinuation Erdos66BracketRankMove Erdos66RankCellExchange
  Erdos66RankProfileGap Erdos66GlobalRankPacketRepair
open scoped Classical
set_option maxHeartbeats 3000000

lemma swapped_downward_exact (A D F : Finset ℕ) (n : ℕ)
    (hD : D ⊆ A) (hF : Disjoint A F)
    (hDhalf : ∀ d∈D, n<2*d) (hpartner : pairs D A n=D.card)
    (hFzero : pairs F A n=0) (hself : sumRep (F : Set ℕ) n=0) :
    sumRep (A : Set ℕ) n=sumRep (swapped A D F : Set ℕ) n+2*D.card := by
  have hdd : sumRep (D : Set ℕ) n=0 := by
    rw [←pairs_self]
    exact pairs_above_half D D n hDhalf hDhalf
  have hDA := pairs_union_right D (A\D) D n Finset.sdiff_disjoint
  rw [Finset.sdiff_union_of_subset hD,hpartner,pairs_self,hdd] at hDA
  have hA := sumRep_union_self (A\D) D n Finset.sdiff_disjoint
  rw [Finset.sdiff_union_of_subset hD,pairs_comm (A\D) D,hdd] at hA
  have hfc := pairs_mono_right (show A\D ⊆ A from Finset.sdiff_subset) (A := F) n
  rw [hFzero,pairs_comm F (A\D)] at hfc
  rw [swapped,sumRep_union_self _ _ _ (hF.mono_left Finset.sdiff_subset),hself]
  omega

lemma swapped_error_le_deletion_and_insertion (A D F : Finset ℕ)
    (hD : D ⊆ A) (hF : Disjoint A F) (z : ℕ) (R : ℝ)
    (hR : insertionEnergy A F z<R) :
    |(sumRep (swapped A D F : Set ℕ) z : ℝ)-sumRep (A : Set ℕ) z|<2*pairs D A z+R := by
  have hu := sumRep_swapped_upper A D F hF z
  have hl := sumRep_swapped_lower A D F hD z
  have hu' : (sumRep (swapped A D F : Set ℕ) z : ℝ) ≤
      sumRep (A : Set ℕ) z+2*pairs F A z+sumRep (F : Set ℕ) z := by exact_mod_cast hu
  have hl' : (sumRep (A : Set ℕ) z : ℝ) ≤
      sumRep (swapped A D F : Set ℕ) z+2*pairs D A z := by exact_mod_cast hl
  have hpos : 0<R := by
    dsimp only [insertionEnergy] at hR
    linarith [Nat.cast_nonneg (α := ℝ) (pairs F A z),Nat.cast_nonneg (α := ℝ) (sumRep (F : Set ℕ) z)]
  dsimp only [insertionEnergy] at hR
  rw [abs_lt]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (pairs D A z)]

/-- All candidate rows correspond to prescribed distinct old ranks. The old
finite set may be a cutoff of the infinite bracket-feasible host. -/
theorem exists_prescribed_rank_relocation {α : Type*} [Fintype α]
    (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L) (A₀ D : Finset ℕ)
    (n m : ℕ) (d : ℕ → ℕ) (f : ℕ → α → ℕ)
    (himage : (Finset.range m).image d=D) (hdinj : Set.InjOn d (Finset.range m : Set ℕ))
    (hD : D ⊆ A₀) (hDhalf : ∀ u∈D, n<2*u) (hpartner : pairs D A₀ n=D.card)
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
      sumRep (A₀ : Set ℕ) n=sumRep (swapped A₀ D F : Set ℕ) n+2*D.card ∧
      ∀ z∈T, |(sumRep (swapped A₀ D F : Set ℕ) z : ℝ)-sumRep (A₀ : Set ℕ) z|<
        2*pairs D A₀ z+5*R z := by
  let assign := fun u ↦ rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)
  have hrows : ∀ i < m, ∀ j < m, i≠j → ∀ a b, f i a≠f j b := by
    intro i hi j hj hij a b he
    have hh := congrArg assign he
    change rankPoint A _ (cell profile (f i a))=rankPoint A _ (cell profile (f j b)) at hh
    rw [hrank i hi a,hrank j hj b] at hh
    exact hij (hdinj (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) hh)
  have hDc : D.card=m := by
    rw [←himage,Finset.card_image_of_injOn hdinj,Finset.card_range]
  obtain ⟨F,hFc,hF,hpoints,hcover,hFA,hFF,hload⟩ := exists_adaptive_singletons A₀ n m f
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
  refine ⟨F,hFc.trans hDc.symm,hF,hFA',hpoints,
    rank_assigned_swap_brackets A hbr D F hFA' hshape.symm hiF,
    swapped_downward_exact A₀ D F n hD hF hDhalf hpartner hFA hFF,?_⟩
  intro z hz
  exact swapped_error_le_deletion_and_insertion A₀ D F hD hF z _ (hload z hz)

end Erdos66PrescribedRankRelocation
