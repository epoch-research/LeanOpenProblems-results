import FormalConjecturesUtil
import Submission.Verified
import Submission.Components

open Filter SimpleGraph Asymptotics

namespace Erdos713Rate
open Finset
universe u

theorem rate_unique {W : Type*} {G : SimpleGraph W} {a b : ℝ}
    (ha : HasRate G a) (hb : HasRate G b) : a = b :=
  le_antisymm (ha.lower b hb.one_le hb.upper) (hb.lower a ha.one_le ha.upper)

theorem rate_of_asymptotic {W : Type*} {G : SimpleGraph W} {a c : ℝ}
    (ha : 1 ≤ a) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n G : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : HasRate G a := by
  refine ⟨ha, (isBigO_const_mul_right_iff hc).mp h.isBigO, ?_⟩
  intro b _ hb
  exact Erdos713Forest.exponent_le_of_isBigO
    (((isBigO_const_mul_left_iff hc).mp h.isBigO_symm).trans hb)

theorem sum_upper {A B : Type*} [Fintype A] [Fintype B] {G : SimpleGraph A} {H : SimpleGraph B}
    {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hG : (fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a))
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ b)) :
    (fun n : ℕ => (extremalNumber n (G ⊕g H) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (max a b)) := by
  have hA := hG.trans (rpow_mono_bigO (le_max_left a b))
  have hB := (shifted_upper (by linarith : 0 ≤ b) (Fintype.card A) hH).trans
    (rpow_mono_bigO (le_max_right a b))
  have hC := cast_linear_bigO (ha.trans (le_max_left a b)) (Fintype.card A)
  apply IsBigO.trans _ ((hA.add hB).add hC)
  apply IsBigO.of_bound 1
  filter_upwards with n
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity), one_mul]
  exact_mod_cast Erdos713Union.extremal_sum_bound G H n

theorem rate_sum_or {A B : Type*} [Fintype A] [Fintype B] {G : SimpleGraph A} {H : SimpleGraph B}
    {r : ℝ} (h : HasRate (G ⊕g H) r) : HasRate G r ∨ HasRate H r := by
  classical
  have huG := (extremal_mono_bigO (show G ⊑ G ⊕g H from ⟨Embedding.sumInl.toCopy⟩)).trans h.upper
  have huH := (extremal_mono_bigO (show H ⊑ G ⊕g H from ⟨Embedding.sumInr.toCopy⟩)).trans h.upper
  by_cases hG : HasRate G r
  · exact Or.inl hG
  right
  refine ⟨h.one_le, huH, ?_⟩
  intro b hb hB
  by_contra hbr
  have hg : ¬∀ a : ℝ, 1 ≤ a →
      ((fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ a)) → r ≤ a := fun hh => hG ⟨h.one_le, huG, hh⟩
  push_neg at hg
  obtain ⟨a, ha, hA, har⟩ := hg
  have hh := h.lower (max a b) (ha.trans (le_max_left _ _)) (sum_upper ha hb hA hB)
  exact (not_lt.mpr hh) (max_lt har (lt_of_not_ge hbr))

theorem nonempty_of_superlinear_rate {W : Type*} [Fintype W] {G : SimpleGraph W}
    {r : ℝ} (hr : 1 < r) (h : HasRate G r) : Nonempty W := by
  by_contra hn
  letI : IsEmpty W := not_nonempty_iff.mp hn
  have hF : G.IsAcyclic := by intro v; exact isEmptyElim v
  have hh := h.lower 1 le_rfl (forest_rate G hF).upper
  exact (not_lt.mpr hh) hr

open scoped Classical in
theorem leaf_rate_converse {W : Type*} [Fintype W] (G : SimpleGraph W)
    {x y : W} (hx : G.degree x = 1) (hxy : G.Adj x y) {r : ℝ}
    (h : HasRate G r) : HasRate (G.induce {x}ᶜ) r := by
  classical
  refine ⟨h.one_le, (extremal_mono_bigO ⟨Copy.induce G _⟩).trans h.upper, ?_⟩
  intro a ha hA
  apply h.lower a ha
  apply IsBigO.trans _ (hA.add (cast_linear_bigO ha (Fintype.card W)))
  apply IsBigO.of_bound 1
  filter_upwards with n
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity), one_mul]
  exact_mod_cast Erdos713Leaf.extremal_leaf_upper G hx hxy n

open scoped Classical in
theorem isolated_rate_converse {W : Type*} [Fintype W] (G : SimpleGraph W)
    {x : W} (hx : G.degree x = 0) {r : ℝ} (h : HasRate G r) : HasRate (G.induce {x}ᶜ) r := by
  classical
  refine ⟨h.one_le, (extremal_mono_bigO ⟨Copy.induce G _⟩).trans h.upper, ?_⟩
  intro a ha hA
  apply h.lower a ha
  apply hA.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (Fintype.card W)] with n hn
  rw [Erdos713Leaf.extremal_isolated_eq G hx hn]

open scoped Classical in
theorem rational_of_reduces {W : Type*} [Fintype W] {G : SimpleGraph W}
    (hG : Erdos713Reduction.Reduces W G) {r : ℝ} (h : HasRate G r) :
    r ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨a, ha⟩ := Erdos713Reduction.exists_rate_of_reduces hG
  exact ⟨a, rate_unique ha h⟩

open scoped Classical in
/-- A superlinear attained growth exponent is carried by a connected subgraph
with minimum degree at least two. The subgraph need not inherit a precise
asymptotic equivalence. -/
theorem exists_connected_core {W : Type u} [Fintype W] (G : SimpleGraph W)
    {r : ℝ} (hr : 1 < r) (h : HasRate G r) :
    ∃ (U : Type u) (_ : Fintype U) (H : SimpleGraph U), H ⊑ G ∧ H.Connected ∧
      (∀ v, 2 ≤ Nat.card (H.neighborSet v)) ∧ HasRate H r ∧ Fintype.card U ≤ Fintype.card W := by
  classical
  suffices hP : ∀ k : ℕ, ∀ (W : Type u) [Fintype W], Fintype.card W = k →
      ∀ G : SimpleGraph W, HasRate G r →
      ∃ (U : Type u) (_ : Fintype U) (H : SimpleGraph U), H ⊑ G ∧ H.Connected ∧
        (∀ v, 2 ≤ Nat.card (H.neighborSet v)) ∧ HasRate H r ∧ Fintype.card U ≤ Fintype.card W from
    hP _ W rfl G h
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro W _ hW G h
    letI : Nonempty W := nonempty_of_superlinear_rate hr h
    have hSmaller (S : Set W) (hs : Nat.card S < k) (hS : HasRate (G.induce S) r) :
        ∃ (U : Type u) (_ : Fintype U) (H : SimpleGraph U), H ⊑ G ∧ H.Connected ∧
          (∀ v, 2 ≤ Nat.card (H.neighborSet v)) ∧ HasRate H r ∧ Fintype.card U ≤ Fintype.card W := by
      obtain ⟨U, inst, H, hHG, hHC, hHD, hHR, hcard⟩ := ih _ (by simpa only [Fintype.card_eq_nat_card] using hs) _ rfl (G.induce S) hS
      exact ⟨U, inst, H, hHG.trans ⟨Copy.induce G S⟩, hHC, hHD, hHR,
        hcard.trans (Fintype.card_subtype_le _)⟩
    by_cases hd : ∀ v, 2 ≤ Nat.card (G.neighborSet v)
    swap
    · push_neg at hd
      obtain ⟨x, hx⟩ := hd
      have hx' : G.degree x < 2 := by
        simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hx
      apply hSmaller {x}ᶜ (by
        simpa only [Fintype.card_eq_nat_card] using
          (Fintype.card_subtype_lt (p := fun v => v ∈ ({x}ᶜ : Set W)) (x := x) (by simp)).trans_eq hW)
      have hx01 : G.degree x = 0 ∨ G.degree x = 1 := by omega
      rcases hx01 with hx0 | hx1
      · exact isolated_rate_converse G hx0 h
      · obtain ⟨y, hxy, _⟩ := degree_eq_one_iff_existsUnique_adj.mp hx1
        exact leaf_rate_converse G hx1 hxy h
    by_cases hC : G.Connected
    · exact ⟨W, inferInstance, G, .refl _, hC, hd, h, le_rfl⟩
    let w : W := Classical.arbitrary W
    have hw : ∃ v, ¬G.Reachable w v := by
      by_contra hhh
      push_neg at hhh
      exact hC ((G.connected_iff_exists_forall_reachable).mpr ⟨w, hhh⟩)
    obtain ⟨v, hv⟩ := hw
    let S : Set W := (G.connectedComponentMk w).supp
    have hwS : w ∈ S := rfl
    have hvS : v ∉ S := by
      intro hh
      exact hv (ConnectedComponent.exact hh.symm)
    have hs : Nat.card S < k := by
      simpa only [Fintype.card_eq_nat_card] using (Fintype.card_subtype_lt hvS).trans_eq hW
    have hsc : Nat.card ↥(Sᶜ) < k := by
      simpa only [Fintype.card_eq_nat_card] using (Fintype.card_subtype_lt (x := w) (by simpa only [Set.mem_compl_iff, not_not] using hwS)).trans_eq hW
    have hSplit := iso_rate (Erdos713Components.splitIso G S (fun u v huv =>
      ConnectedComponent.mem_supp_congr_adj (G.connectedComponentMk w) huv)) h
    rcases rate_sum_or hSplit with hS | hSc
    · exact hSmaller S hs hS
    · exact hSmaller Sᶜ hsc hSc

theorem rate_upper_of_containment {W : Type*} {H : SimpleGraph W}
    {s t : ℕ} (hs : 1 ≤ s) (hH : H ⊑ Erdos713KST.Kst s t) {a : ℝ} (h : HasRate H a) :
    a ≤ 2 - 1 / (s : ℝ) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have he : ((s - 1 + s : ℕ) : ℝ) / (s : ℝ) = 2 - 1 / (s : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub hs, Nat.cast_one]
    field_simp
    ring
  rw [← he]
  apply h.lower
  · apply (le_div_iff₀ hs').mpr
    rw [one_mul]
    exact_mod_cast (show s ≤ s - 1 + s by omega)
  · apply (extremal_mono_bigO hH).trans
    exact upper_of_power_bound (by omega) (fun n => Erdos713KST.extremal_pow_le s t n hs)

theorem rate_bipartite_upper {W : Type*} [Fintype W] [Nonempty W]
    {H : SimpleGraph W} (hB : H.IsBipartite) {a : ℝ} (h : HasRate H a) :
    a ≤ 2 - 1 / (Fintype.card W : ℝ) :=
  rate_upper_of_containment Fintype.card_pos (Erdos713KST.bipartite_contained H hB) h

open scoped Classical in
theorem rate_alteration_lower {W : Type*} [Fintype W] (H : SimpleGraph W)
    (he : 2 ≤ H.edgeFinset.card) (hq : 2 ≤ Fintype.card W)
    (hqe : Fintype.card W ≤ 2 * H.edgeFinset.card) {a : ℝ} (h : HasRate H a) :
    2 - ((Fintype.card W : ℝ) - 2) / ((H.edgeFinset.card : ℝ) - 1) ≤ a := by
  have he1 : 1 ≤ H.edgeFinset.card := by omega
  have hp : (0 : ℝ) < (H.edgeFinset.card : ℝ) - 1 := by
    have hh : (2 : ℝ) ≤ H.edgeFinset.card := by exact_mod_cast he
    linarith
  have hh := Erdos713Alteration.exponent_lower_of_power_sequence (f := fun n => extremalNumber n H)
    (s := H.edgeFinset.card - 1) (m := 2 * H.edgeFinset.card - Fintype.card W) (C := 64)
    (by omega) (fun t ht => Erdos713Alteration.power_sequence_lower H he hq hqe t ht) h.upper
  rw [Nat.cast_sub hqe, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub he1, Nat.cast_one] at hh
  have heq : 2 - ((Fintype.card W : ℝ) - 2) / ((H.edgeFinset.card : ℝ) - 1) =
      (2 * (H.edgeFinset.card : ℝ) - (Fintype.card W : ℝ)) / ((H.edgeFinset.card : ℝ) - 1) := by
    field_simp [hp.ne']
    ring
  rwa [heq]

end Erdos713Rate

#print axioms Erdos713Rate.rate_sum_or
#print axioms Erdos713Rate.leaf_rate_converse
#print axioms Erdos713Rate.isolated_rate_converse

#print axioms Erdos713Rate.exists_connected_core

#print axioms Erdos713Rate.rate_alteration_lower
#print axioms Erdos713Rate.rate_upper_of_containment
