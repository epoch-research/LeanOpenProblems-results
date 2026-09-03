import Submission.LeafReduction

/-!
# Preservation of superlinear power asymptotics under leaf deletion

The linear error from the graph-theoretic leaf reduction is negligible relative
to a positive power law with exponent greater than one. Thus the exponent and
the exact leading coefficient survive deleting a leaf or an isolated vertex.
This does not settle rationality for the remaining cyclic cores.
-/

open Filter Asymptotics SimpleGraph
open scoped Topology

namespace Erdos713Core

universe u

lemma natCast_isLittleO_rpow {a : ℝ} (ha : 1 < a) :
    (fun n : ℕ => (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ a) := by
  apply (isLittleO_iff_tendsto' ?_).mpr
  · have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(a - 1))) atTop (𝓝 (0 : ℝ)) :=
      (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp tendsto_natCast_atTop_atTop
    apply ht.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [neg_sub, Real.rpow_sub hn', Real.rpow_one]
  · filter_upwards [eventually_gt_atTop 0] with n hn hzero
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    exact ((Real.rpow_pos_of_pos hn' a).ne' hzero).elim

/-- An `O(n)` error preserves a superlinear pure-power asymptotic, including its coefficient. -/
lemma equivalent_of_sub_isBigO_natCast {f g : ℕ → ℝ} {a c : ℝ}
    (ha : 1 < a) (hc : c ≠ 0)
    (hf : f ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ a))
    (hdiff : (f - g) =O[atTop] (fun n : ℕ => (n : ℝ))) :
    g ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ a) := by
  have hd := hdiff.trans_isLittleO ((natCast_isLittleO_rpow ha).const_mul_right hc)
  simpa only [sub_sub_cancel] using hf.sub_isLittleO hd

/-- The real-valued change in extremal number on deleting a leaf is `O(n)`. -/
lemma extremalNumber_sub_leaf_isBigO {W : Type u} [Fintype W]
    {H : SimpleGraph W} {v w : W} (hvw : H.Adj v w)
    (hleaf : ∀ z, H.Adj v z → z = w) :
    ((fun n : ℕ => (extremalNumber n H : ℝ)) -
      (fun n : ℕ => (extremalNumber n (H.induce ({v}ᶜ : Set W)) : ℝ))) =O[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  apply IsBigO.of_bound (Fintype.card W : ℝ)
  filter_upwards [] with n
  obtain ⟨hl, hu⟩ := Erdos713LeafReduction.extremalNumber_leaf_bounds hvw hleaf n
  have hl' : (extremalNumber n (H.induce ({v}ᶜ : Set W)) : ℝ) ≤ extremalNumber n H := by
    exact_mod_cast hl
  have hu' : (extremalNumber n H : ℝ) ≤
      (extremalNumber n (H.induce ({v}ᶜ : Set W)) : ℝ) +
        (Fintype.card W : ℝ) * (n : ℝ) := by exact_mod_cast hu
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hl'), Nat.abs_cast]
  linarith

/-- Deleting a leaf preserves exactly the same superlinear exponent and coefficient. -/
theorem equivalent_induce_compl_leaf {W : Type u} [Fintype W]
    {H : SimpleGraph W} {v w : W} (hvw : H.Adj v w)
    (hleaf : ∀ z, H.Adj v z → z = w) {a c : ℝ} (ha : 1 < a) (hc : 0 < c)
    (hf : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) :
    (fun n : ℕ => (extremalNumber n (H.induce ({v}ᶜ : Set W)) : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a) :=
  equivalent_of_sub_isBigO_natCast ha hc.ne' hf (extremalNumber_sub_leaf_isBigO hvw hleaf)

/-- Deleting an isolated vertex preserves every given power asymptotic. -/
theorem equivalent_induce_compl_isolated {W : Type u} [Fintype W]
    {H : SimpleGraph W} {v : W} (hv : ∀ z, ¬ H.Adj v z) {a c : ℝ}
    (hf : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) :
    (fun n : ℕ => (extremalNumber n (H.induce ({v}ᶜ : Set W)) : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a) := by
  apply hf.congr_left
  filter_upwards [Erdos713LeafReduction.eventually_extremalNumber_eq_of_isolated hv] with n hn
  exact congrArg (fun k : ℕ => (k : ℝ)) hn

/-- Deleting any vertex of degree at most one preserves a superlinear asymptotic. -/
theorem equivalent_induce_compl_of_degree_le_one {W : Type u} [Fintype W]
    {H : SimpleGraph W} [DecidableRel H.Adj] {v : W} (hv : H.degree v ≤ 1)
    {a c : ℝ} (ha : 1 < a) (hc : 0 < c)
    (hf : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) :
    (fun n : ℕ => (extremalNumber n (H.induce ({v}ᶜ : Set W)) : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a) := by
  by_cases hv0 : H.degree v = 0
  · apply equivalent_induce_compl_isolated (hf := hf)
    intro z hvz
    have hp := hvz.degree_pos_left
    omega
  · have hv1 : H.degree v = 1 := by omega
    obtain ⟨w, hvw, hleaf⟩ := degree_eq_one_iff_existsUnique_adj.mp hv1
    exact equivalent_induce_compl_leaf hvw hleaf ha hc hf

open scoped Classical in
/-- A superlinear pure-power asymptotic of a finite bipartite forbidden graph
also occurs, with exactly the same coefficient, for a contained finite graph
whose vertices all have degree at least two. This is only a reduction to cores. -/
theorem exists_min_degree_core {W : Type u} [Fintype W]
    (H : SimpleGraph W) (hBip : H.IsBipartite) {a c : ℝ} (ha : 1 < a) (hc : 0 < c)
    (hf : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) :
    ∃ q : ℕ, ∃ G : SimpleGraph (Fin q), q ≤ Fintype.card W ∧ G ⊑ H ∧
      G.IsBipartite ∧ (∀ x, 2 ≤ G.degree x) ∧
      (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
        (fun n : ℕ => c * (n : ℝ) ^ a) := by
  classical
  induction hn : Fintype.card W using Nat.strong_induction_on generalizing W with
  | h k ih =>
    by_cases hdeg : ∀ x, 2 ≤ H.degree x
    · let e := Fintype.equivFin W
      let G : SimpleGraph (Fin (Fintype.card W)) := H.map e.toEmbedding
      letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
      refine ⟨Fintype.card W, G, hn.le, ⟨(Iso.map e H).symm.toCopy⟩,
        hBip.map e.toEmbedding, ?_, ?_⟩
      · intro x
        have heq := (Iso.map e H).degree_eq (e.symm x)
        change G.degree (e (e.symm x)) = H.degree (e.symm x) at heq
        rw [e.apply_symm_apply] at heq
        exact (hdeg (e.symm x)).trans_eq heq.symm
      · apply hf.congr_left
        filter_upwards [] with n
        exact congrArg (fun m : ℕ => (m : ℝ))
          (extremalNumber_congr_right (n := n) (Iso.map e H))
    · push_neg at hdeg
      obtain ⟨v, hv⟩ := hdeg
      let S : Set W := {v}ᶜ
      have hsize : Fintype.card S < k := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := v) (by simp [S])
      have hBipS : (H.induce S).IsBipartite :=
        ⟨hBip.some.comp (Copy.induce H S).toHom⟩
      have hfS := equivalent_induce_compl_of_degree_le_one (by omega : H.degree v ≤ 1)
        ha hc hf
      obtain ⟨q, G, hq, hGH, hBG, hDG, hfG⟩ :=
        ih (Fintype.card S) hsize (H.induce S) hBipS hfS rfl
      refine ⟨q, G, hq.trans hsize.le,
        hGH.trans ⟨Copy.induce H S⟩, hBG, hDG, hfG⟩

/-- An empty forbidden graph is contained in every host. -/
lemma extremalNumber_eq_zero_of_isEmpty {W : Type u} [IsEmpty W]
    (H : SimpleGraph W) (n : ℕ) : extremalNumber n H = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ hfree
  exact (hfree IsContained.of_isEmpty).elim

lemma not_zero_equivalent_rpow {a c : ℝ} (hc : 0 < c) :
    ¬ (fun _ : ℕ => (0 : ℝ)) ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ a) := by
  intro h
  have hz := isEquivalent_zero_iff_eventually_zero.mp h.symm
  obtain ⟨n, hn, hnpos⟩ := (hz.and (eventually_gt_atTop 0)).exists
  have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
  exact (mul_pos hc (Real.rpow_pos_of_pos hnpos' a)).ne' hn

open scoped Classical in
/-- A minimum-degree-two core with a positive power asymptotic really has at
least two edges; the vacuous empty-vertex case cannot satisfy that asymptotic. -/
lemma core_two_le_edge_card {q : ℕ} (G : SimpleGraph (Fin q))
    (hdeg : ∀ x, 2 ≤ G.degree x) {a c : ℝ} (hc : 0 < c)
    (hf : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) : 2 ≤ G.edgeFinset.card := by
  classical
  by_cases hq : q = 0
  · subst q
    apply (not_zero_equivalent_rpow hc).elim
    simpa only [extremalNumber_eq_zero_of_isEmpty, Nat.cast_zero] using hf
  · letI : NeZero q := ⟨hq⟩
    exact (hdeg 0).trans (G.degree_le_card_edgeFinset 0)

open scoped Classical in
/-- It suffices to prove rationality for the nonempty minimum-degree-two cores
with exponent strictly between one and two. The core assertion is an explicit
hypothesis here, not an asserted solution of the original conjecture. -/
theorem rationality_of_core_case
    (hCore : ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite →
      2 ≤ G.edgeFinset.card → (∀ x, 2 ≤ G.degree x) →
      ∀ a c : ℝ, a ∈ Set.Ioo 1 2 → 0 < c →
        (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
          (fun n : ℕ => c * (n : ℝ) ^ a) →
        a ∈ Set.range ((↑) : ℚ → ℝ))
    {W : Type u} [Fintype W] (H : SimpleGraph W) (hBip : H.IsBipartite)
    {a c : ℝ} (ha : a ∈ Set.Ico 1 2) (hc : 0 < c)
    (hf : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  by_cases ha1 : a = 1
  · exact ⟨1, by simpa using ha1.symm⟩
  · have hagt : 1 < a := lt_of_le_of_ne ha.1 (Ne.symm ha1)
    obtain ⟨q, G, _, _, hBG, hDG, hfG⟩ := exists_min_degree_core H hBip hagt hc hf
    exact hCore q G hBG (core_two_le_edge_card G hDG hc hfG) hDG a c ⟨hagt, ha.2⟩ hc hfG



end Erdos713Core

#print axioms Erdos713Core.equivalent_induce_compl_leaf
#print axioms Erdos713Core.equivalent_induce_compl_isolated
