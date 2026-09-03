import Submission.IntervalRowSingletonSelectionExplore
import Submission.DisjointWindowMassExplore
import Submission.GlobalRankPacketRepairExplore
import Submission.RankCellWindowExplore

/-! Restoring original rank cells with one common insertion-load potential.
No central partner hypothesis is imposed on the prescribed deletion set. -/
namespace Erdos66AggregatedRankRestorationSelection
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66FiniteSwapAlgebra
  Erdos66AdaptiveSingletonAlgebra Erdos66IntervalRowSingletonSelection Erdos66DisjointWindowMass
  Erdos66Counting Erdos66OrderedPartialReplacement Erdos66Fractional
  Erdos66ClampedPrefixContinuation Erdos66BracketRankMove Erdos66RankCellExchange
  Erdos66RankProfileGap Erdos66GlobalRankPacketRepair
open scoped Classical
set_option maxHeartbeats 3000000

theorem exists_aggregated_rank_restoration
    (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L) (A₀ D : Finset ℕ)
    (hA₀ : (A₀ : Set ℕ) ⊆ A) (w m : ℕ) (d L : ℕ → ℕ)
    (himage : (Finset.range m).image d=D) (hdinj : Set.InjOn d (Finset.range m : Set ℕ))
    (hrank : ∀ k < m, ∀ i : Fin w,
      rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile (L k+i.val))=d k)
    (hcut : ∀ k < m, ∀ i : Fin w, L k+i.val∈A ↔ L k+i.val∈A₀)
    (B : ℝ)
    (hB : ∀ k < m, ((Finset.univ.filter (fun i : Fin w ↦ L k+i.val∈A₀)).card : ℝ) ≤ B)
    (T : Finset ℕ) (q t : ℝ) (R : ℕ → ℝ) (hq : 0<q) (ht : 0<t)
    (hbudget : q+B ≤ w)
    (hsmall : (∑ z∈T, Real.exp
      (Real.exp t*((∑ i∈Finset.range (m*w), profile i)+5*m)/q-t*R z))<1) :
    ∃ F : Finset ℕ, F.card=D.card ∧ Disjoint A₀ F ∧ Disjoint (F : Set ℕ) A ∧
      (∀ u∈F, ∃ k < m, ∃ i : Fin w, u=L k+i.val) ∧
      (∀ N, PrefixBrackets profile (swap A D F) N) ∧
      ∀ z∈T, insertionEnergy A₀ F z < 5*R z := by
  let f (k : ℕ) (i : Fin w) := L k+i.val
  let assign := fun u ↦ rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)
  have hrows : ∀ i < m, ∀ j < m, i≠j → ∀ a b, f i a≠f j b := by
    intro i hi j hj hij a b he
    have hh := congrArg assign he
    change rankPoint A _ (cell profile (f i a))=rankPoint A _ (cell profile (f j b)) at hh
    rw [hrank i hi a,hrank j hj b] at hh
    exact hij (hdinj (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) hh)
  have hDc : D.card=m := by
    rw [←himage,Finset.card_image_of_injOn hdinj,Finset.card_range]
  have hsep : ∀ i < m, ∀ j < m, i≠j → L i+w ≤ L j ∨ L j+w ≤ L i := by
    intro i hi j hj hij
    by_contra hn
    simp only [not_or,not_le] at hn
    let u := max (L i) (L j)
    have hui : L i ≤ u := le_max_left _ _
    have huj : L j ≤ u := le_max_right _ _
    have huhi : u < L i+w := by dsimp only [u]; omega
    have huhj : u < L j+w := by dsimp only [u]; omega
    let a : Fin w := ⟨u-L i,by omega⟩
    let b : Fin w := ⟨u-L j,by omega⟩
    apply hrows i hi j hj hij a b
    dsimp only [f,a,b]
    omega
  let K (k z : ℕ) : ℝ := (partnerChoices A₀ (f k) z).card
  have hsum (z : ℕ) : (∑ k∈Finset.range m, Real.exp t*(K k z+3)/q) ≤
      Real.exp t*((∑ i∈Finset.range (m*w), profile i)+5*m)/q := by
    have hh := sum_partnerChoices_bound profile profile_antitone profile_nonneg A hbr A₀ hA₀ L w m hsep z
    change (∑ k∈Finset.range m, K k z) ≤ 2*m+∑ i∈Finset.range (m*w), profile i at hh
    rw [←Finset.sum_div,←Finset.mul_sum,Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith :
        (∑ k∈Finset.range m, K k z)+(m : ℝ)*3 ≤ (∑ i∈Finset.range (m*w), profile i)+5*m)
        (Real.exp_pos t).le) hq.le
  have hsmall' : (∑ z∈T, Real.exp
      ((∑ k∈Finset.range m, Real.exp t*(K k z+3)/q)-t*R z))<1 :=
    (Finset.sum_le_sum (fun z _ ↦ Real.exp_le_exp.mpr (sub_le_sub_right (hsum z) _))).trans_lt hsmall
  obtain ⟨F,hFc,hF,hpoints,hcover,hload⟩ := exists_interval_singletons A₀ L w m hsep
    B q t T K R hq ht hB hbudget (fun _ _ _ _ ↦ le_rfl) hsmall'
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

end Erdos66AggregatedRankRestorationSelection
