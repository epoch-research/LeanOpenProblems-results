import FormalConjecturesUtil

/-!
# The forest case of the conditional extremal-exponent question

This file proves the elementary linear extremal bound for every finite forest.
It does not resolve the corresponding question for arbitrary bipartite graphs.
The embedding argument uses a spanning tree extension and induction by removing a leaf.
-/

open Filter Asymptotics SimpleGraph

namespace Erdos713Forest

universe u v

/-- A finite forest on a nonempty vertex type extends to a spanning tree. -/
lemma exists_tree_extension {W : Type u} [Finite W] [Nonempty W]
    {H : SimpleGraph W} (hH : H.IsAcyclic) :
    ∃ T : SimpleGraph W, H ≤ T ∧ T.IsTree := by
  obtain ⟨T, hHT, hT⟩ := Finite.exists_le_maximal hH
  exact ⟨T, hHT, maximal_isAcyclic_iff_isTree.mp hT⟩

/-- A nonempty host of minimum degree at least the number of vertices of a finite tree
contains that tree. The deliberately non-sharp degree threshold simplifies the counting. -/
lemma tree_isContained_of_degree {W : Type u} {V : Type v}
    [Fintype W] [Fintype V] [Nonempty V]
    (T : SimpleGraph W) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : T.IsTree) (hdeg : ∀ x, Fintype.card W ≤ G.degree x) : T ⊑ G := by
  classical
  induction hn : Fintype.card W using Nat.strong_induction_on generalizing W with
  | h n ih =>
    rw [hn] at hdeg
    rcases subsingleton_or_nontrivial W with hW | hW
    · letI := hW
      let x : V := Classical.choice inferInstance
      refine ⟨⟨⟨fun _ => x, ?_⟩, ?_⟩⟩
      · intro a b hab
        exact (hab.ne (Subsingleton.elim a b)).elim
      · intro a b _
        exact Subsingleton.elim a b
    · letI := hW
      obtain ⟨w, hw⟩ := hT.exists_vert_degree_one_of_nontrivial
      obtain ⟨z, hwz, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hw
      let S : Set W := {w}ᶜ
      have hcard : Fintype.card S < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := w) (by simp [S])
      have hTS : (T.induce S).IsTree :=
        ⟨hT.isConnected.induce_compl_singleton_of_degree_eq_one hw, hT.IsAcyclic.induce S⟩
      obtain ⟨f⟩ := ih (Fintype.card S) hcard (T.induce S) hTS
        (fun x => (Nat.le_of_lt hcard).trans (hdeg x)) rfl
      have hz : z ∈ S := by simpa [S] using hwz.ne.symm
      let used : Finset V := Finset.univ.image f
      have hused : used.card < (G.neighborFinset (f ⟨z, hz⟩)).card := by
        calc
          used.card ≤ Fintype.card S := Finset.card_image_le.trans_eq (Finset.card_univ)
          _ < n := hcard
          _ ≤ (G.neighborFinset (f ⟨z, hz⟩)).card := hdeg _
      obtain ⟨x, hxadj, hxunused⟩ := Finset.exists_mem_notMem_of_card_lt_card hused
      have hxadj' : G.Adj (f ⟨z, hz⟩) x := by simpa using hxadj
      have hx : ∀ a : S, x ≠ f a := by
        intro a heq
        apply hxunused
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, heq.symm⟩
      let g : W → V := fun a => if ha : a = w then x else f ⟨a, by simpa [S] using ha⟩
      refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
      · intro a b hab
        by_cases ha : a = w
        · subst a
          have hb : b ≠ w := hab.ne.symm
          have hbz : b = z := huniq b hab
          subst b
          simpa [g, hb] using hxadj'.symm
        · by_cases hb : b = w
          · subst b
            have haz : a = z := huniq a hab.symm
            subst a
            simpa [g, ha] using hxadj'
          · simpa [g, ha, hb] using f.toHom.map_adj (show (T.induce S).Adj
              ⟨a, by simpa [S] using ha⟩ ⟨b, by simpa [S] using hb⟩ from hab)
      · intro a b hab
        by_cases ha : a = w
        · by_cases hb : b = w
          · exact ha.trans hb.symm
          · have heq : x = f ⟨b, by simpa [S] using hb⟩ := by simpa [g, ha, hb] using hab
            exact (hx _ heq).elim
        · by_cases hb : b = w
          · have heq : f ⟨a, by simpa [S] using ha⟩ = x := by simpa [g, ha, hb] using hab
            exact (hx _ heq.symm).elim
          · have heq : f ⟨a, by simpa [S] using ha⟩ = f ⟨b, by simpa [S] using hb⟩ := by
              simpa [g, ha, hb] using hab
            exact congrArg Subtype.val (f.injective heq)

/-- Every finite forest embeds in a nonempty host whose degrees are at least the
number of vertices of the forest. This includes the empty forest. -/
lemma forest_isContained_of_degree {W : Type u} {V : Type v}
    [Fintype W] [Fintype V] [Nonempty V]
    (H : SimpleGraph W) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hH : H.IsAcyclic) (hdeg : ∀ x, Fintype.card W ≤ G.degree x) : H ⊑ G := by
  classical
  rcases isEmpty_or_nonempty W with hW | hW
  · letI := hW
    refine ⟨⟨⟨fun w => isEmptyElim w, ?_⟩, ?_⟩⟩
    · intro a b _
      exact isEmptyElim a
    · intro a b _
      exact isEmptyElim a
  · letI := hW
    obtain ⟨T, hHT, hT⟩ := exists_tree_extension hH
    exact (IsContained.of_le hHT).trans (tree_isContained_of_degree T G hT hdeg)

/-- A nonempty finite graph avoiding a forest has a vertex of degree less than the
number of vertices of that forest. -/
lemma exists_degree_lt_of_free_forest {W : Type u} {V : Type v}
    [Fintype W] [Fintype V] [Nonempty V]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel G.Adj]
    (hH : H.IsAcyclic) (hfree : H.Free G) :
    ∃ x, G.degree x < Fintype.card W := by
  by_contra! hdeg
  exact hfree (forest_isContained_of_degree H G hH hdeg)

/-- The elementary linear extremal bound for every finite forest, including disconnected
forests, isolated vertices, and the empty forest. -/
theorem extremalNumber_le_card_mul {W : Type u} [Fintype W]
    (H : SimpleGraph W) (hH : H.IsAcyclic) (n : ℕ) :
    extremalNumber n H ≤ Fintype.card W * n := by
  classical
  induction n with
  | zero =>
    rw [← Fintype.card_fin 0, extremalNumber_le_iff]
    intro G _ _
    have hG : G = ⊥ := Subsingleton.elim _ _
    simp [hG]
  | succ n ih =>
    rw [← Fintype.card_fin (n + 1), extremalNumber_le_iff]
    intro G _ hfree
    obtain ⟨x, hx⟩ := exists_degree_lt_of_free_forest hH hfree
    have hdel := card_edgeFinset_deleteIncidenceSet_le_extremalNumber hfree x
    rw [card_edgeFinset_deleteIncidenceSet, Fintype.card_fin, Nat.add_sub_cancel] at hdel
    have hbound := hdel.trans ih
    have hdegree := G.degree_le_card_edgeFinset x
    simp only [Fintype.card_fin, Nat.mul_succ]
    omega

/-- Explicit constant `C_H = q` for a forest on `Fin q`. -/
theorem extremalNumber_le_mul {q : ℕ} (H : SimpleGraph (Fin q))
    (hH : H.IsAcyclic) (n : ℕ) : extremalNumber n H ≤ q * n := by
  simpa only [Fintype.card_fin] using extremalNumber_le_card_mul H hH n

/-- The corresponding edge bound for any finite graph avoiding a fixed finite forest. -/
theorem card_edges_le_card_mul_of_free_forest {W : Type u} {V : Type v}
    [Fintype W] [Fintype V]
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel G.Adj]
    (hH : H.IsAcyclic) (hfree : H.Free G) :
    G.edgeFinset.card ≤ Fintype.card W * Fintype.card V :=
  (card_edgeFinset_le_extremalNumber hfree).trans
    (extremalNumber_le_card_mul H hH (Fintype.card V))

/-- The real-valued extremal function of a finite forest is `O(n)`. -/
theorem extremalNumber_isBigO_natCast {W : Type u} [Fintype W]
    (H : SimpleGraph W) (hH : H.IsAcyclic) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  refine IsBigO.of_bound (Fintype.card W) (Filter.Eventually.of_forall ?_)
  intro n
  have h : (extremalNumber n H : ℝ) ≤ (Fintype.card W : ℝ) * (n : ℝ) := by
    exact_mod_cast extremalNumber_le_card_mul H hH n
  simpa using h

/-- A Big-O comparison of real powers on the natural numbers orders their exponents.
This is proved here to keep the forest file independent of other submission files. -/
lemma exponent_le_of_isBigO {a b : ℝ}
    (h : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ b)) : a ≤ b := by
  by_contra hab
  have hba : 0 < a - b := sub_pos.mpr (lt_of_not_ge hab)
  obtain ⟨C, hC⟩ := isBigO_iff.mp h
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (a - b)) atTop atTop :=
    (tendsto_rpow_atTop hba).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn, hnC, hnpos⟩ :=
    (hC.and ((ht.eventually_gt_atTop C).and (eventually_gt_atTop 0))).exists
  have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hpow : 0 < (n : ℝ) ^ b := Real.rpow_pos_of_pos hnpos' _
  simp only [Real.norm_eq_abs, abs_of_pos hpow,
    abs_of_pos (Real.rpow_pos_of_pos hnpos' a)] at hn
  rw [Real.rpow_sub hnpos'] at hnC
  exact (not_lt_of_ge ((div_le_iff₀ hpow).mpr hn)) hnC

/-- If the extremal function of a finite forest is asymptotic to `c * n ^ a`, with
`c > 0` and `a ≥ 1`, then its exponent is exactly `1`. No upper bound on `a` is needed. -/
theorem exponent_eq_one_of_equivalent {W : Type u} [Fintype W]
    (H : SimpleGraph W) (hH : H.IsAcyclic) {a c : ℝ}
    (ha : 1 ≤ a) (hc : 0 < c)
    (heq : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = 1 := by
  apply le_antisymm _ ha
  apply exponent_le_of_isBigO
  have h : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop] (fun n : ℕ => (n : ℝ)) :=
    (heq.isTheta.of_const_mul_right hc.ne').symm.isBigO.trans
      (extremalNumber_isBigO_natCast H hH)
  simpa only [Real.rpow_one] using h

/-- The conditional rational-exponent conclusion for all forests on `Fin q`.
Unlike the general bipartite problem, this special case follows from an elementary linear bound. -/
theorem rational_exponent_of_equivalent {q : ℕ} (H : SimpleGraph (Fin q))
    (hH : H.IsAcyclic) {a c : ℝ} (ha : 1 ≤ a) (hc : 0 < c)
    (heq : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨1, ?_⟩
  simpa using (exponent_eq_one_of_equivalent H hH ha hc heq).symm

end Erdos713Forest
