import Submission.GlobalRankPacketRepairExplore

/-! Far-target errors of many edits in one short interval are controlled by
old interval occupancy, not by the number of edits. -/
namespace Erdos66ShortSupportSwapTail
open Filter AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66FiniteSwapAlgebra
  Erdos66PredecessorCutoffTransfer Erdos66Counting Erdos66ReflectionRoundingPatch
  Erdos66Fractional Erdos66Rounding Erdos66Generating Erdos66FlatProfileWindows
  Erdos66BracketOrderedExchange Erdos66ClampedPrefixContinuation
  Erdos66OrderedPartialReplacement
open scoped Classical Topology
set_option maxHeartbeats 2800000

lemma brackets_count_discrepancy (p : ℕ → ℝ) (A : Set ℕ)
    (hbr : ∀ L, PrefixBrackets p A L) (X : ℕ) :
    |(count A X : ℝ)-cumulative p X| ≤ 1 := by
  have hb := hbr X X le_rfl
  rw [mass_indicator_eq_count] at hb
  have hf := Int.lt_floor_add_one (mass p X)
  have hc := Int.ceil_lt_add_one (mass p X)
  change |(count A X : ℝ)-mass p X| ≤ 1
  rw [abs_le]
  constructor <;> linarith

lemma supported_pairs_le_window (A : Set ℕ) (B P : Finset ℕ) (U z : ℕ)
    (hBA : (B : Set ℕ) ⊆ A) (hP : ∀ u∈P, u<U) :
    pairs P B z ≤ (intervalPart A (z+1-U) (z+1)).card := by
  rw [pairs_eq_filter]
  apply Finset.card_le_card_of_injOn (fun u ↦ z-u)
  · intro u hu
    obtain ⟨hu,huz,hub⟩ := Finset.mem_filter.mp hu
    have hs := hP u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,hBA hub⟩
  · intro u hu v hv he
    have hu' := (Finset.mem_filter.mp hu).2.1
    have hv' := (Finset.mem_filter.mp hv).2.1
    dsimp only at he
    omega

lemma supported_self_zero (F : Finset ℕ) (U z : ℕ)
    (hF : ∀ u∈F, u<U) (hz : 2*U ≤ z) : sumRep (F : Set ℕ) z=0 := by
  rw [←pairs_self]
  apply pairs_eq_zero_of_no_partner
  intro u hu huz huv
  have h1 := hF u hu
  have h2 := hF (z-u) huv
  omega

/-- Equal cardinalities are not needed for this tail estimate. -/
lemma short_support_swap_error (A : Set ℕ) (D F : Finset ℕ) (U z : ℕ)
    (hD : (D : Set ℕ) ⊆ A) (hF : Disjoint (F : Set ℕ) A)
    (hs : ∀ u∈D∪F, u<U) (hz : 2*U ≤ z) :
    |(sumRep (swap A D F) z : ℝ)-sumRep A z| ≤
      2*(intervalPart A (z+1-U) (z+1)).card := by
  let B := cutoff A (z+1)
  have hBA : (B : Set ℕ) ⊆ A := fun u hu ↦ (mem_cutoff.mp hu).2
  have hDB : D ⊆ B := by
    intro u hu
    have hh := hs u (Finset.mem_union_left _ hu)
    exact mem_cutoff.mpr ⟨by omega,hD hu⟩
  have hFB : Disjoint B F := Finset.disjoint_left.mpr (fun u hu hv ↦ Set.disjoint_left.mp hF hv (hBA hu))
  have hu := sumRep_swapped_upper B D F hFB z
  have hl := sumRep_swapped_lower B D F hDB z
  have h0 := supported_self_zero F U z (fun u hu ↦ hs u (Finset.mem_union_right _ hu)) hz
  have hd := supported_pairs_le_window A B D U z hBA (fun u hu ↦ hs u (Finset.mem_union_left _ hu))
  have hf := supported_pairs_le_window A B F U z hBA (fun u hu ↦ hs u (Finset.mem_union_right _ hu))
  have hnew : sumRep (swapped B D F : Set ℕ) z=sumRep (swap A D F) z := cutoff_swap_rep A D F (by omega)
  have hold : sumRep (B : Set ℕ) z=sumRep A z := cutoff_rep A (by omega)
  rw [hnew,hold,h0] at hu
  rw [hnew,hold] at hl
  have hu' : (sumRep (swap A D F) z : ℝ) ≤ sumRep A z+2*(intervalPart A (z+1-U) (z+1)).card := by
    exact_mod_cast (show sumRep (swap A D F) z ≤ sumRep A z+2*(intervalPart A (z+1-U) (z+1)).card by omega)
  have hl' : (sumRep A z : ℝ) ≤ sumRep (swap A D F) z+2*(intervalPart A (z+1-U) (z+1)).card := by
    exact_mod_cast (show sumRep A z ≤ sumRep (swap A D F) z+2*(intervalPart A (z+1-U) (z+1)).card by omega)
  rw [abs_le]
  constructor <;> linarith

lemma antitone_window_count (p : ℕ → ℝ) (A : Set ℕ) (D : ℝ)
    (hanti : Antitone p) (hbal : ∀ X, |(count A X : ℝ)-cumulative p X| ≤ D)
    (a U : ℕ) :
    ((intervalPart A a (a+U)).card : ℝ) ≤ U*p a+2*D := by
  have hc := (abs_le.mp (local_count_error A p D hbal a (a+U) (by omega))).2
  have hm : (∑ i∈Finset.Ico a (a+U), p i) ≤ (U : ℝ)*p a := by
    calc
      _ ≤ ∑ _i∈Finset.Ico a (a+U), p a :=
        Finset.sum_le_sum (fun i hi ↦ hanti (Finset.mem_Ico.mp hi).1)
      _ = _ := by simp
  linarith

lemma short_support_profile_error (p : ℕ → ℝ) (A : Set ℕ) (D F : Finset ℕ)
    (δ : ℝ) (hanti : Antitone p)
    (hbal : ∀ X, |(count A X : ℝ)-cumulative p X| ≤ δ)
    (hD : (D : Set ℕ) ⊆ A) (hF : Disjoint (F : Set ℕ) A)
    (U z : ℕ) (hs : ∀ u∈D∪F, u<U) (hz : 2*U ≤ z) :
    |(sumRep (swap A D F) z : ℝ)-sumRep A z| ≤ 2*((U : ℝ)*p (z+1-U)+2*δ) := by
  have hc := antitone_window_count p A δ hanti hbal (z+1-U) U
  rw [show z+1-U+U=z+1 by omega] at hc
  exact (short_support_swap_error A D F U z hD hF hs hz).trans
    (mul_le_mul_of_nonneg_left hc (by norm_num))

/-- A fixed polynomial horizon suffices for arbitrarily many edits supported
below 15N+1. The bound is uniform in the edited cardinalities. -/
theorem eventually_harmonic_short_support_tail :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Set ℕ), (∀ L, PrefixBrackets profile A L) →
      ∀ D F : Finset ℕ, (D : Set ℕ) ⊆ A → Disjoint (F : Set ℕ) A →
      (∀ u∈D∪F, u ≤ 15*N) → ∀ z, N^33+1 ≤ z →
      |(sumRep (swap A D F) z : ℝ)-sumRep A z| ≤ 6 := by
  filter_upwards [eventually_ge_atTop 32,eventually_harmonic_polynomial_bound] with N hN hH
  have hNp : 0<N := by omega
  have hN1 : 1 ≤ N := by omega
  have hp := (profile_polynomial_bounds N (by omega) hH).1
  have h15 : 15*N+1 ≤ N^15 := by
    have hh := Nat.pow_le_pow_right hNp (show 2 ≤ 15 by norm_num)
    have hlow : 15*N+1 ≤ N^2 := by nlinarith
    exact hlow.trans hh
  have h32 : 16*N+2 ≤ N^32 := by
    have hh := Nat.pow_le_pow_right hNp (show 2 ≤ 32 by norm_num)
    have hlow : 16*N+2 ≤ N^2 := by nlinarith
    exact hlow.trans hh
  have h33 : N^33=N^32*N := by rw [show 33=32+1 by norm_num,Nat.pow_succ]
  intro A hbr D F hD hF hs z hz
  have hfar : N^32 ≤ z+1-(15*N+1) := by
    have ht := Nat.mul_le_mul_left (N^32) (show 2 ≤ N by omega)
    rw [h33] at hz
    have hh : N^32+(15*N+1) ≤ z+1 := by nlinarith
    omega
  have hzU : 2*(15*N+1) ≤ z := by rw [h33] at hz; nlinarith
  have hbound : ((15*N+1 : ℕ) : ℝ)*profile (z+1-(15*N+1)) ≤ 1 := by
    calc
      _ ≤ ((15*N+1 : ℕ) : ℝ)*profile (N^32) :=
        mul_le_mul_of_nonneg_left (profile_antitone hfar) (Nat.cast_nonneg _)
      _ ≤ (N : ℝ)^15*profile (N^32) := by
        apply mul_le_mul_of_nonneg_right _ (profile_nonneg _)
        exact_mod_cast h15
      _ ≤ 1 := hp
  have he := short_support_profile_error profile A D F 1 profile_antitone
    (brackets_count_discrepancy profile A hbr) hD hF (15*N+1) z (fun u hu ↦ by have := hs u hu; omega) hzU
  linarith

end Erdos66ShortSupportSwapTail
