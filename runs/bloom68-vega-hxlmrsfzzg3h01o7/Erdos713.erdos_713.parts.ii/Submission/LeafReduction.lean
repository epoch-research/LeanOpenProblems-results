import FormalConjecturesUtil

/-!
# A general leaf-deletion reduction for extremal numbers

For every finite graph `H` and every leaf `v` of `H`, deleting `v` changes the
extremal number by at most `Fintype.card W * n`. The argument keeps the host
vertex type fixed, so it also applies when the forbidden graph has isolated
vertices. In particular, the leaf may belong to an isolated `K₂` component.
Deleting an isolated forbidden vertex preserves the extremal number for
`n ≥ Fintype.card W`.

This is a reduction, not a solution of the extremal-exponent problem for
arbitrary bipartite graphs. No bipartiteness assumption is needed here.
-/

open SimpleGraph

namespace Erdos713LeafReduction

universe u v

/-- Delete incidence sets at vertices of positive degree less than `q`. The host
vertex type is unchanged, and the total number of lost edges is at most `q`
times the original number of nonisolated vertices. -/
lemma exists_le_min_positive_degree {V : Type v} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) :
    ∃ G₀ : SimpleGraph V, ∃ _ : DecidableRel G₀.Adj, G₀ ≤ G ∧
      (∀ x, 0 < G₀.degree x → q ≤ G₀.degree x) ∧
      G.edgeFinset.card ≤ G₀.edgeFinset.card + q * Fintype.card G.support := by
  classical
  induction hm : Fintype.card G.support using Nat.strong_induction_on generalizing G with
  | h m ih =>
    by_cases hdeg : ∀ x, 0 < G.degree x → q ≤ G.degree x
    · exact ⟨G, inferInstance, le_rfl, hdeg, Nat.le_add_right _ _⟩
    push_neg at hdeg
    obtain ⟨x, hpos, hx⟩ := hdeg
    have hxS : x ∈ G.support := (G.degree_pos_iff_mem_support x).mp hpos
    have hcardpos : 0 < Fintype.card G.support :=
      Fintype.card_pos_iff.mpr ⟨⟨x, hxS⟩⟩
    have hsupport := G.card_support_deleteIncidenceSet hxS
    have hlt : Fintype.card (G.deleteIncidenceSet x).support < m := by omega
    obtain ⟨G₀, inst, hsub, hdeg, hbound⟩ :=
      ih (Fintype.card (G.deleteIncidenceSet x).support) hlt (G.deleteIncidenceSet x) rfl
    refine ⟨G₀, inst, hsub.trans (G.deleteIncidenceSet_le x), hdeg, ?_⟩
    have hmul : q * Fintype.card (G.deleteIncidenceSet x).support + q ≤
        q * Fintype.card G.support := by
      have hcard : Fintype.card (G.deleteIncidenceSet x).support + 1 ≤
          Fintype.card G.support := by omega
      simpa only [Nat.mul_add, Nat.mul_one] using Nat.mul_le_mul_left q hcard
    rw [hm] at hmul
    have hedge := G.card_edgeFinset_deleteIncidenceSet x
    have hdegree := G.degree_le_card_edgeFinset x
    omega

/-- Reinsert a leaf once the image of its parent has enough neighbors. -/
lemma isContained_of_leaf_copy {W : Type u} {V : Type v}
    [Fintype W] [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    [DecidableRel G.Adj] {v : W} (p : ({v}ᶜ : Set W))
    (hleaf : ∀ a, H.Adj v a → a = p.1)
    (f : (H.induce ({v}ᶜ : Set W)).Copy G)
    (hdeg : Fintype.card W ≤ G.degree (f p)) : H ⊑ G := by
  classical
  let S : Set W := {v}ᶜ
  have hcard : Fintype.card S < Fintype.card W :=
    Fintype.card_subtype_lt (x := v) (by simp [S])
  let used : Finset V := Finset.univ.image f
  have hused : used.card < (G.neighborFinset (f p)).card := by
    calc
      used.card ≤ Fintype.card S := Finset.card_image_le.trans_eq Finset.card_univ
      _ < Fintype.card W := hcard
      _ ≤ (G.neighborFinset (f p)).card := hdeg
  obtain ⟨x, hxadj, hxunused⟩ := Finset.exists_mem_notMem_of_card_lt_card hused
  have hxadj' : G.Adj (f p) x := by simpa using hxadj
  have hx : ∀ a : S, x ≠ f a := by
    intro a heq
    exact hxunused (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, heq.symm⟩)
  let g : W → V := fun a => if ha : a = v then x else f ⟨a, by simpa [S] using ha⟩
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · intro a b hab
    by_cases ha : a = v
    · subst a
      have hb : b ≠ v := hab.ne.symm
      have hbp : b = p.1 := hleaf b hab
      subst b
      simpa [g, hb] using hxadj'.symm
    · by_cases hb : b = v
      · subst b
        have hap : a = p.1 := hleaf a hab.symm
        subst a
        simpa [g, ha] using hxadj'
      · simpa [g, ha, hb] using f.toHom.map_adj (show (H.induce S).Adj
          ⟨a, by simpa [S] using ha⟩ ⟨b, by simpa [S] using hb⟩ from hab)
  · intro a b hab
    by_cases ha : a = v
    · by_cases hb : b = v
      · exact ha.trans hb.symm
      · have heq : x = f ⟨b, by simpa [S] using hb⟩ := by simpa [g, ha, hb] using hab
        exact (hx _ heq).elim
    · by_cases hb : b = v
      · have heq : f ⟨a, by simpa [S] using ha⟩ = x := by simpa [g, ha, hb] using hab
        exact (hx _ heq.symm).elim
      · have heq : f ⟨a, by simpa [S] using ha⟩ = f ⟨b, by simpa [S] using hb⟩ := by
          simpa [g, ha, hb] using hab
        exact congrArg Subtype.val (f.injective heq)

/-- In a nonempty-edge host with large positive degrees, a designated vertex of
any copy can be made nonisolated. If its original image is isolated, the vertex
itself has no incident edges in the copied graph, so it can be moved to an
unused neighbor of a nonisolated host vertex. -/
lemma exists_copy_degree_pos {A : Type u} {V : Type v}
    [Fintype A] [Fintype V] {F : SimpleGraph A} {G : SimpleGraph V}
    [DecidableRel G.Adj] (hG : G ≠ ⊥)
    (hdeg : ∀ x, 0 < G.degree x → Fintype.card A < G.degree x)
    (f : F.Copy G) (p : A) : ∃ f' : F.Copy G, 0 < G.degree (f' p) := by
  classical
  by_cases hpos : 0 < G.degree (f p)
  · exact ⟨f, hpos⟩
  obtain ⟨a, b, hab⟩ := ne_bot_iff_exists_adj.mp hG
  let used : Finset V := Finset.univ.image f
  have hused : used.card < (G.neighborFinset a).card := by
    calc
      used.card ≤ Fintype.card A := Finset.card_image_le.trans_eq Finset.card_univ
      _ < (G.neighborFinset a).card := hdeg a hab.degree_pos_left
  obtain ⟨y, hyadj, hyunused⟩ := Finset.exists_mem_notMem_of_card_lt_card hused
  have hyadj' : G.Adj a y := by simpa using hyadj
  have hy : ∀ z : A, y ≠ f z := by
    intro z heq
    exact hyunused (Finset.mem_image.mpr ⟨z, Finset.mem_univ _, heq.symm⟩)
  have hnop : ∀ z, ¬ F.Adj p z := by
    intro z hpz
    exact hpos (f.toHom.map_adj hpz).degree_pos_left
  let g : A → V := fun z => if z = p then y else f z
  let hg : F.Copy G := by
    refine ⟨⟨g, ?_⟩, ?_⟩
    · intro z t hzt
      have hz : z ≠ p := by rintro rfl; exact hnop t hzt
      have ht : t ≠ p := by rintro rfl; exact hnop z hzt.symm
      simpa only [g, if_neg hz, if_neg ht] using f.toHom.map_adj hzt
    · intro z t hzt
      by_cases hz : z = p
      · by_cases ht : t = p
        · exact hz.trans ht.symm
        · have heq : y = f t := by simpa [g, hz, ht] using hzt
          exact (hy _ heq).elim
      · by_cases ht : t = p
        · have heq : f z = y := by simpa [g, hz, ht] using hzt
          exact (hy _ heq.symm).elim
        · apply f.injective
          simpa [g, hz, ht] using hzt
  have hgp : hg p = y := by
    change (if p = p then y else f p) = y
    rw [if_pos rfl]
  refine ⟨hg, ?_⟩
  rw [hgp]
  exact hyadj'.degree_pos_right

/-- A copy of the leaf-deleted graph extends in any nonempty-edge host whose
positive degrees are at least the order of `H`. This includes an isolated
`K₂` component: its parent is remapped if necessary. -/
lemma isContained_of_leaf_of_min_positive_degree {W : Type u} {V : Type v}
    [Fintype W] [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    [DecidableRel G.Adj] {v w : W} (hvw : H.Adj v w)
    (hleaf : ∀ a, H.Adj v a → a = w) (hG : G ≠ ⊥)
    (hdeg : ∀ x, 0 < G.degree x → Fintype.card W ≤ G.degree x)
    (hcopy : H.induce ({v}ᶜ : Set W) ⊑ G) : H ⊑ G := by
  classical
  let p : ({v}ᶜ : Set W) := ⟨w, by simpa using hvw.ne.symm⟩
  have hcard : Fintype.card ({v}ᶜ : Set W) < Fintype.card W :=
    Fintype.card_subtype_lt (x := v) (by simp)
  obtain ⟨f⟩ := hcopy
  obtain ⟨f', hf'⟩ := exists_copy_degree_pos hG (fun x hx => hcard.trans_le (hdeg x hx)) f p
  exact isContained_of_leaf_copy p hleaf f' (hdeg _ hf')

/-- The fixed-host leaf bound, with the error charged only to the original
nonisolated vertices. No monotonicity in the size of the host is used. -/
theorem card_edges_le_leaf_extremalNumber_add_support {W : Type u} {V : Type v}
    [Fintype W] [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    [DecidableRel G.Adj] {v w : W} (hvw : H.Adj v w)
    (hleaf : ∀ a, H.Adj v a → a = w) (hfree : H.Free G) :
    G.edgeFinset.card ≤ extremalNumber (Fintype.card V) (H.induce ({v}ᶜ : Set W)) +
      Fintype.card W * Fintype.card G.support := by
  classical
  obtain ⟨G₀, inst, hsub, hdeg, hbound⟩ := exists_le_min_positive_degree G (Fintype.card W)
  have hcore : G₀.edgeFinset.card ≤
      extremalNumber (Fintype.card V) (H.induce ({v}ᶜ : Set W)) := by
    by_cases hG₀ : G₀ = ⊥
    · have hedge₀ : G₀.edgeFinset = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        have he' : e ∈ G₀.edgeSet := mem_edgeFinset.mp he
        simp only [hG₀, edgeSet_bot, Set.mem_empty_iff_false] at he'
      rw [hedge₀, Finset.card_empty]
      exact Nat.zero_le _
    · apply card_edgeFinset_le_extremalNumber
      intro hcopy
      exact hfree ((isContained_of_leaf_of_min_positive_degree hvw hleaf hG₀ hdeg hcopy).mono_right hsub)
  exact hbound.trans (Nat.add_le_add_right hcore _)

/-- Every induced vertex-deletion of the forbidden graph has no larger extremal
number. This is monotonicity in the forbidden graph, not in the host order. -/
theorem extremalNumber_induce_compl_singleton_le {W : Type u}
    (H : SimpleGraph W) (v : W) (n : ℕ) :
    extremalNumber n (H.induce ({v}ᶜ : Set W)) ≤ extremalNumber n H :=
  (show H.induce ({v}ᶜ : Set W) ⊑ H from ⟨Copy.induce H _⟩).extremalNumber_le

/-- Deleting an arbitrary leaf changes the extremal number by at most a linear
term. Other components and isolated vertices are allowed, including the case
where the leaf and its parent form an isolated `K₂` component. -/
theorem extremalNumber_le_leaf_add {W : Type u} [Fintype W]
    {H : SimpleGraph W} {v w : W} (hvw : H.Adj v w)
    (hleaf : ∀ a, H.Adj v a → a = w) (n : ℕ) :
    extremalNumber n H ≤ extremalNumber n (H.induce ({v}ᶜ : Set W)) + Fintype.card W * n := by
  classical
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ hfree
  exact (card_edges_le_leaf_extremalNumber_add_support hvw hleaf hfree).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Fintype.card_subtype_le _)) _)

/-- The general finite leaf-deletion reduction, with both bounds in one statement.
There are no assumptions of bipartiteness, connectivity, or nonisolation of the
parent after deletion. The inequalities hold for every `n`, including `0`. -/
theorem extremalNumber_leaf_bounds {W : Type u} [Fintype W]
    {H : SimpleGraph W} {v w : W} (hvw : H.Adj v w)
    (hleaf : ∀ a, H.Adj v a → a = w) (n : ℕ) :
    extremalNumber n (H.induce ({v}ᶜ : Set W)) ≤ extremalNumber n H ∧
      extremalNumber n H ≤ extremalNumber n (H.induce ({v}ᶜ : Set W)) + Fintype.card W * n :=
  ⟨extremalNumber_induce_compl_singleton_le H v n, extremalNumber_le_leaf_add hvw hleaf n⟩

/-- A formulation using the intrinsic condition that the deleted vertex has
degree one, without having to supply its unique neighbor. -/
theorem extremalNumber_leaf_bounds_of_degree_one {W : Type u} [Fintype W]
    {H : SimpleGraph W} [DecidableRel H.Adj] {v : W} (hv : H.degree v = 1) (n : ℕ) :
    extremalNumber n (H.induce ({v}ᶜ : Set W)) ≤ extremalNumber n H ∧
      extremalNumber n H ≤ extremalNumber n (H.induce ({v}ᶜ : Set W)) + Fintype.card W * n := by
  obtain ⟨w, hvw, hleaf⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
  exact extremalNumber_leaf_bounds hvw hleaf n

/-- The reduction for forbidden graphs on `Fin q`, with the explicit error `q * n`. -/
theorem extremalNumber_leaf_bounds_fin {q : ℕ} {H : SimpleGraph (Fin q)}
    {v w : Fin q} (hvw : H.Adj v w) (hleaf : ∀ a, H.Adj v a → a = w) (n : ℕ) :
    extremalNumber n (H.induce ({v}ᶜ : Set (Fin q))) ≤ extremalNumber n H ∧
      extremalNumber n H ≤ extremalNumber n (H.induce ({v}ᶜ : Set (Fin q))) + q * n := by
  simpa only [Fintype.card_fin] using extremalNumber_leaf_bounds hvw hleaf n

/-- A `Finite`-type variant, using `Nat.card` instead of a chosen enumeration. -/
theorem extremalNumber_leaf_bounds_finite {W : Type u} [Finite W]
    {H : SimpleGraph W} {v w : W} (hvw : H.Adj v w)
    (hleaf : ∀ a, H.Adj v a → a = w) (n : ℕ) :
    extremalNumber n (H.induce ({v}ᶜ : Set W)) ≤ extremalNumber n H ∧
      extremalNumber n H ≤ extremalNumber n (H.induce ({v}ᶜ : Set W)) + Nat.card W * n := by
  classical
  letI := Fintype.ofFinite W
  simpa only [Nat.card_eq_fintype_card] using extremalNumber_leaf_bounds hvw hleaf n

/-- Reinsert an isolated vertex in a copy when the host has at least as many
vertices as the forbidden graph. -/
lemma isContained_of_isolated_induce {W : Type u} {V : Type v}
    [Fintype W] [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V} {v : W}
    (hv : ∀ a, ¬ H.Adj v a) (hcard : Fintype.card W ≤ Fintype.card V)
    (hcopy : H.induce ({v}ᶜ : Set W) ⊑ G) : H ⊑ G := by
  classical
  obtain ⟨f⟩ := hcopy
  let S : Set W := {v}ᶜ
  have hS : Fintype.card S < Fintype.card W :=
    Fintype.card_subtype_lt (x := v) (by simp [S])
  let used : Finset V := Finset.univ.image f
  have hused : used.card < (Finset.univ : Finset V).card := by
    calc
      used.card ≤ Fintype.card S := Finset.card_image_le.trans_eq Finset.card_univ
      _ < Fintype.card W := hS
      _ ≤ (Finset.univ : Finset V).card := by simpa only [Finset.card_univ] using hcard
  obtain ⟨x, _, hxunused⟩ := Finset.exists_mem_notMem_of_card_lt_card hused
  have hx : ∀ a : S, x ≠ f a := by
    intro a heq
    exact hxunused (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, heq.symm⟩)
  let g : W → V := fun a => if ha : a = v then x else f ⟨a, by simpa [S] using ha⟩
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · intro a b hab
    have ha : a ≠ v := by rintro rfl; exact hv b hab
    have hb : b ≠ v := by rintro rfl; exact hv a hab.symm
    simpa [g, ha, hb] using f.toHom.map_adj (show (H.induce S).Adj
      ⟨a, by simpa [S] using ha⟩ ⟨b, by simpa [S] using hb⟩ from hab)
  · intro a b hab
    by_cases ha : a = v
    · by_cases hb : b = v
      · exact ha.trans hb.symm
      · have heq : x = f ⟨b, by simpa [S] using hb⟩ := by simpa [g, ha, hb] using hab
        exact (hx _ heq).elim
    · by_cases hb : b = v
      · have heq : f ⟨a, by simpa [S] using ha⟩ = x := by simpa [g, ha, hb] using hab
        exact (hx _ heq.symm).elim
      · have heq : f ⟨a, by simpa [S] using ha⟩ = f ⟨b, by simpa [S] using hb⟩ := by
          simpa [g, ha, hb] using hab
        exact congrArg Subtype.val (f.injective heq)

/-- Deleting an isolated forbidden vertex leaves the extremal number unchanged
for every host order `n ≥ Fintype.card W`. The size hypothesis is essential for
isolated vertices and is not replaced by any global monotonicity assertion. -/
theorem extremalNumber_eq_induce_of_isolated {W : Type u} [Fintype W]
    {H : SimpleGraph W} {v : W} (hv : ∀ a, ¬ H.Adj v a)
    {n : ℕ} (hn : Fintype.card W ≤ n) :
    extremalNumber n H = extremalNumber n (H.induce ({v}ᶜ : Set W)) := by
  classical
  apply le_antisymm _ (extremalNumber_induce_compl_singleton_le H v n)
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ hfree
  apply card_edgeFinset_le_extremalNumber
  intro hcopy
  exact hfree (isContained_of_isolated_induce hv (by simpa only [Fintype.card_fin] using hn) hcopy)

/-- In particular, deleting an isolated forbidden vertex gives eventual equality
of the two extremal functions. -/
theorem eventually_extremalNumber_eq_of_isolated {W : Type u} [Fintype W]
    {H : SimpleGraph W} {v : W} (hv : ∀ a, ¬ H.Adj v a) :
    ∀ᶠ n in Filter.atTop,
      extremalNumber n H = extremalNumber n (H.induce ({v}ᶜ : Set W)) :=
  Filter.eventually_atTop.mpr ⟨Fintype.card W, fun _ hn => extremalNumber_eq_induce_of_isolated hv hn⟩

end Erdos713LeafReduction

#print axioms Erdos713LeafReduction.extremalNumber_leaf_bounds
#print axioms Erdos713LeafReduction.extremalNumber_leaf_bounds_finite
#print axioms Erdos713LeafReduction.extremalNumber_eq_induce_of_isolated
#print axioms Erdos713LeafReduction.eventually_extremalNumber_eq_of_isolated
