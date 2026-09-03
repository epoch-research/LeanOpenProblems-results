import Submission.SymmetricRowPeakExplore

/-! Reflection peaks persist for antitone position-dependent palettes whose
members share one reflection. These are restrictions on a row construction,
not on arbitrary sets of natural numbers. -/
namespace Erdos66AntitoneRowPeak
open AdditiveCombinatorics Erdos66SymmetricRowPeak Erdos66TranslatedPrefixPalette
  Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 1600000

variable (p : ℕ) [NeZero p]

noncomputable def upperSelected (X : Finset (ZMod p)) (t : ZMod p) : Finset (ZMod p) :=
  X.filter (fun x ↦ (t-x).val<x.val)

lemma integerRow_mono {X Y : Finset (ZMod p)} (h : X ⊆ Y) (a : ℕ) :
    integerRow p X a ⊆ integerRow p Y a := by
  apply Set.image_mono
  intro n hn
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
  exact Finset.mem_image.mpr ⟨x, h hx, rfl⟩

/-- It suffices that the selected point with larger representative always
brings its reflected partner. Full symmetry of the selected set is not needed. -/
theorem directed_row_peak (X : Finset (ZMod p)) (t : ZMod p) (a : ℕ)
    (hpair : ∀ x∈X, (t-x).val<x.val → t-x∈X)
    (A : Set ℕ) (hA : integerRow p X a ⊆ A) :
    ∃ n : ℕ, 2*a ≤ n ∧ n<2*(a+p) ∧ (upperSelected p X t).card ≤ sumRep A n := by
  let U := upperSelected p X t
  let V := U.image (fun x ↦ t-x)
  have hdis : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨y, hUy, rfl⟩ := Finset.mem_image.mp hy
    have hh := (Finset.mem_filter.mp hx).2
    have hh' := (Finset.mem_filter.mp hUy).2
    simp only [sub_sub_cancel] at hh
    exact (lt_trans hh hh').false
  have hinj : Function.Injective (fun x : ZMod p ↦ t-x) := by
    intro x y hxy
    exact sub_right_injective hxy
  have hcard : (U∪V).card = 2*U.card := by
    rw [Finset.card_union_of_disjoint hdis, show V.card=U.card from
      Finset.card_image_of_injective _ hinj]
    omega
  have hsub : U∪V ⊆ X := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).1
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact hpair y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2
  have hs : ∀ x∈U∪V, t-x∈U∪V := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      simpa only [sub_sub_cancel] using Finset.mem_union_left V hy
  obtain ⟨n, hn₀, hn₁, hn⟩ := symmetric_row_peak p (U∪V) t a hs A
    ((integerRow_mono p hsub a).trans hA)
  rw [hcard] at hn
  exact ⟨n, hn₀, hn₁, show U.card ≤ sumRep A n by omega⟩

noncomputable def selected (C : ℕ → Finset (ZMod p)) : Finset (ZMod p) :=
  Finset.univ.filter (fun x ↦ x∈C x.val)

@[simp] lemma mem_selected (C : ℕ → Finset (ZMod p)) (x : ZMod p) :
    x∈selected p C ↔ x∈C x.val := by simp [selected]

lemma antitone_selected_partner (C : ℕ → Finset (ZMod p)) (t : ZMod p)
    (hanti : ∀ i j, i≤j → j<p → C j ⊆ C i)
    (hsym : ∀ i<p, ∀ x∈C i, t-x∈C i) :
    ∀ x∈selected p C, (t-x).val<x.val → t-x∈selected p C := by
  intro x hx hlt
  rw [mem_selected] at hx ⊢
  exact hanti _ _ hlt.le (ZMod.val_lt x) (hsym _ (ZMod.val_lt x) x hx)

/-- Varying a common-phase symmetric palette antitonically within a row does
not eliminate the reflection peak produced by its selected upper endpoints. -/
theorem antitone_row_peak (C : ℕ → Finset (ZMod p)) (t : ZMod p)
    (hanti : ∀ i j, i≤j → j<p → C j ⊆ C i)
    (hsym : ∀ i<p, ∀ x∈C i, t-x∈C i)
    (a : ℕ) (A : Set ℕ) (hA : integerRow p (selected p C) a ⊆ A) :
    ∃ n : ℕ, 2*a ≤ n ∧ n<2*(a+p) ∧
      (upperSelected p (selected p C) t).card ≤ sumRep A n :=
  directed_row_peak p (selected p C) t a (antitone_selected_partner p C t hanti hsym) A hA

theorem antitone_row_log_envelope (C : ℕ → Finset (ZMod p)) (t : ZMod p)
    (hanti : ∀ i j, i≤j → j<p → C j ⊆ C i)
    (hsym : ∀ i<p, ∀ x∈C i, t-x∈C i)
    (a : ℕ) (A : Set ℕ) (hA : integerRow p (selected p C) a ⊆ A)
    (K c : ℝ) (hc : 0≤c)
    (henv : ∀ n : ℕ, (sumRep A n:ℝ) ≤ K+c*Real.log (n+2)) :
    ((upperSelected p (selected p C) t).card:ℝ) ≤ K+c*Real.log (2*(a+p)+2) := by
  obtain ⟨n, hn₀, hn₁, hn⟩ := antitone_row_peak p C t hanti hsym a A hA
  have hh : ((upperSelected p (selected p C) t).card:ℝ) ≤ (sumRep A n:ℝ) := by
    exact_mod_cast hn
  have hl : Real.log ((n:ℝ)+2) ≤ Real.log (2*((a:ℝ)+p)+2) := by
    apply Real.log_le_log (by positivity)
    have hn' : (n:ℝ)<2*((a:ℝ)+p) := by exact_mod_cast hn₁
    linarith
  exact hh.trans ((henv n).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hl hc)))

lemma neg_upper_iff (x : ZMod p) : (0-x).val<x.val ↔ p<2*x.val := by
  rw [zero_sub]
  by_cases hx : x=0
  · subst x
    simp
  · letI : NeZero x := ⟨hx⟩
    rw [ZMod.val_neg_of_ne_zero]
    have hh := ZMod.val_lt x
    omega

lemma parabolaRow_mono [Fact p.Prime] {U V : Finset (ZMod p)}
    (hUV : U ⊆ V) (y : ZMod p) : parabolaRow p U y ⊆ parabolaRow p V y := by
  intro x hx
  simp only [parabolaRow, parabolaSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨u, hu, he⟩ := hx
  exact ⟨u, hUV hu, he⟩

/-- One horizontal phase is allowed, but it must be shared by the palette
members on this row. Independent position-dependent phases are not covered. -/
theorem antitone_translated_parabola_row_peak [Fact p.Prime]
    (U : ℕ → Finset (ZMod p)) (y s : ZMod p)
    (hU : ∀ i j, i≤j → j<p → U j ⊆ U i)
    (a : ℕ) (A : Set ℕ)
    (hA : integerRow p (selected p (fun i ↦
      Erdos66TranslatedPrefixPalette.shift p (parabolaRow p (U i) y) s)) a ⊆ A) :
    ∃ n : ℕ, 2*a ≤ n ∧ n<2*(a+p) ∧
      (upperSelected p (selected p (fun i ↦
        Erdos66TranslatedPrefixPalette.shift p (parabolaRow p (U i) y) s)) (2*s)).card ≤
          sumRep A n := by
  apply antitone_row_peak p _ (2*s) _ _ a A hA
  · intro i j hij hj
    exact Finset.image_subset_image (parabolaRow_mono p (hU i j hij hj) y)
  · intro i hi
    simpa only [add_zero] using shifted_reflection p (parabolaRow p (U i) y) s 0
      (fun x hx ↦ by simpa only [zero_sub] using parabolaRow_neg p (U i) y x hx)

end Erdos66AntitoneRowPeak
