import Mathlib

set_option autoImplicit false

/-!
# Common-list marked forests

Complete independent formalization of the finite common-list marked-forest
theorem CL from `CommonMarkedForestCL.md`.  An embedding always means an injective
homomorphism (`SimpleGraph.Copy`), not an induced embedding.  This file does not
import `Submission.Spec`.
-/

open Finset SimpleGraph Classical

namespace CommonMarkedForest

universe u v w

section FiniteSets

variable {W : Type v} [Fintype W] (H : SimpleGraph W)

/-- Deleting a finite set loses at most its cardinality many neighbors. -/
lemma degree_le_remaining_add (D : Finset W) (s : W) :
    H.degree s ≤ (H.neighborFinset s \ D).card + D.card := by
  have h := Finset.card_sdiff_add_card_inter (H.neighborFinset s) D
  have hi := Finset.card_le_card (Finset.inter_subset_right (s₁ := H.neighborFinset s) (s₂ := D))
  rw [H.card_neighborFinset_eq_degree] at h
  omega

/-- One saved neighbor improves the deletion bound by one. -/
lemma degree_lt_remaining_add_of_miss (D : Finset W) (s t : W)
    (ht : t ∈ D) (hnt : ¬ H.Adj s t) :
    H.degree s < (H.neighborFinset s \ D).card + D.card := by
  have h := Finset.card_sdiff_add_card_inter (H.neighborFinset s) D
  have hi : (H.neighborFinset s ∩ D).card < D.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, ?_⟩
    intro he
    have : t ∈ H.neighborFinset s ∩ D := he.symm ▸ ht
    exact hnt (H.mem_neighborFinset s t |>.mp (Finset.mem_inter.mp this).1)
  rw [H.card_neighborFinset_eq_degree] at h
  omega

/-- Induced degrees expressed using the original vertex type. -/
lemma degree_induce_compl (D : Finset W) (s : ↑((D : Set W)ᶜ)) :
    (H.induce (D : Set W)ᶜ).degree s = (H.neighborFinset s \ D).card := by
  have h := H.map_neighborFinset_induce (s := (D : Set W)ᶜ) s
  have hc := congrArg Finset.card h
  simpa [Finset.sdiff_eq_inter_compl] using hc

/-- A used set containing the parent has at most `|U|-1` occupied neighbors. -/
lemma fresh_neighbor (U : Finset W) (s : W) (hs : s ∈ U)
    (hdeg : U.card ≤ H.degree s) :
    ∃ t, H.Adj s t ∧ t ∉ U := by
  have h := degree_lt_remaining_add_of_miss H U s s hs H.irrefl
  have hp : 0 < (H.neighborFinset s \ U).card := by omega
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hp
  exact ⟨t, by simpa using (Finset.mem_sdiff.mp ht).1, (Finset.mem_sdiff.mp ht).2⟩

end FiniteSets

section TreeExtension

variable {V : Type u} [Fintype V] {T : SimpleGraph V}

/-- Every nontrivial finite tree has a leaf distinct from a specified root. -/
lemma exists_leaf_ne (hT : T.IsTree) (r : V) [Nontrivial V] :
    ∃ l : V, l ≠ r ∧ T.degree l = 1 := by
  by_contra! hn
  have hpos (x : V) : 0 < T.degree x :=
    hT.isConnected.preconnected.degree_pos_of_nontrivial x
  have htwo : ∀ x ∈ (univ : Finset V).erase r, 2 ≤ T.degree x := by
    intro x hx
    have hxne : x ≠ r := (Finset.mem_erase.mp hx).1
    have := hn x hxne
    have := hpos x
    omega
  have hs := Finset.sum_le_sum htwo
  have he := Finset.sum_erase_add (univ : Finset V) (fun x => T.degree x) (mem_univ r)
  have hc : ((univ : Finset V).erase r).card + 1 = Fintype.card V := by
    simpa using Finset.card_erase_add_one (mem_univ r)
  have ht := hT.card_edgeFinset
  have hd := T.sum_degrees_eq_twice_card_edges
  have hr := hpos r
  simp only [sum_const, nsmul_eq_mul] at hs
  simp only [Nat.cast_id] at hs
  dsimp at he
  omega

/-- Removing a leaf gives a smaller tree; the root is not removed. -/
lemma tree_delete_leaf (hT : T.IsTree) {l : V} (hl : T.degree l = 1) :
    (T.induce {l}ᶜ).IsTree :=
  ⟨hT.isConnected.induce_compl_singleton_of_degree_eq_one hl, hT.IsAcyclic.induce _⟩

omit [Fintype V] in
/-- Extend a copy of a leaf-deleted graph by one fresh adjacent vertex. -/
lemma extend_leaf {W : Type v} (H : SimpleGraph W) {l p : V}
    (hlp : T.Adj l p) (hl : ∀ x, T.Adj l x → x = p)
    (g : (T.induce {l}ᶜ).Copy H) (s : W)
    (hs : s ∉ Set.range g)
    (hadj : H.Adj s (g ⟨p, hlp.ne.symm⟩)) :
    ∃ f : T.Copy H, f l = s ∧ ∀ x : ({l}ᶜ : Set V), f x = g x := by
  let f : V → W := fun x => if hx : x = l then s else g ⟨x, hx⟩
  have hf (x : ({l}ᶜ : Set V)) : f x = g x := by
    simp [f, show x.val ≠ l from x.property]
  refine ⟨⟨⟨f, ?_⟩, ?_⟩, ?_, hf⟩
  · intro x y hxy
    by_cases hx : x = l
    · subst x
      have hy := hl y hxy
      subst y
      simpa [f, hlp.ne.symm] using hadj
    · by_cases hy : y = l
      · subst y
        have hp := hl x hxy.symm
        subst x
        simpa [f, hlp.ne.symm] using hadj.symm
      · simpa [f, hx, hy] using g.toHom.map_rel' (show (T.induce {l}ᶜ).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
  · intro x y hxy
    by_cases hx : x = l
    · by_cases hy : y = l
      · exact hx.trans hy.symm
      · have he : s = g ⟨y, hy⟩ := by simpa [f, hx, hy] using hxy
        exact (hs ⟨⟨y, hy⟩, he.symm⟩).elim
    · by_cases hy : y = l
      · have he : g ⟨x, hx⟩ = s := by simpa [f, hx, hy] using hxy
        exact (hs ⟨⟨x, hx⟩, he⟩).elim
      · have he : g ⟨x, hx⟩ = g ⟨y, hy⟩ := by simpa [f, hx, hy] using hxy
        exact congrArg Subtype.val (g.injective he)
  · simp [f]

/-- A generic greedy extension criterion, including prescribed root image. -/
lemma tree_copy_of_fresh {W : Type v} (H : SimpleGraph W)
    (hT : T.IsTree) (r : V) (s₀ : W)
    (hfresh : ∀ U : Finset W, s₀ ∈ U → U.card < Fintype.card V →
      ∀ s ∈ U, ∃ t, H.Adj s t ∧ t ∉ U) :
    ∃ f : T.Copy H, f r = s₀ := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hsub : Subsingleton V
    · letI := hsub
      refine ⟨⟨⟨fun _ => s₀, ?_⟩, ?_⟩, rfl⟩
      · intro x y hxy
        exact (hxy.ne (Subsingleton.elim x y)).elim
      · intro x y _
        exact Subsingleton.elim x y
    · letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨l, hlr, hl⟩ := exists_leaf_ne hT r
      obtain ⟨p, hlp, hp⟩ := degree_eq_one_iff_existsUnique_adj.mp hl
      have hc : Fintype.card ({l}ᶜ : Set V) < Fintype.card V :=
        Fintype.card_subtype_lt (x := l) (by simp)
      obtain ⟨g, hgr⟩ := ih (Fintype.card ({l}ᶜ : Set V)) (by omega) (tree_delete_leaf hT hl)
        (⟨r, Ne.symm hlr⟩ : ({l}ᶜ : Set V))
        (fun U hU hcard => hfresh U hU (hcard.trans hc)) rfl
      let U : Finset W := univ.image g
      have hu (x : ({l}ᶜ : Set V)) : g x ∈ U := mem_image.mpr ⟨x, mem_univ _, rfl⟩
      have hur : s₀ ∈ U := hgr ▸ hu ⟨r, Ne.symm hlr⟩
      have huc : U.card < Fintype.card V := by
        change (univ.image g).card < Fintype.card V
        rw [card_image_of_injective (f := g) _ g.injective, card_univ]
        exact hc
      obtain ⟨s, hps, hs⟩ := hfresh U hur huc _ (hu ⟨p, hlp.ne.symm⟩)
      obtain ⟨f, _, hfg⟩ := extend_leaf H hlp hp g s
        (by rintro ⟨x, rfl⟩; exact hs (hu x)) hps.symm
      exact ⟨f, (hfg ⟨r, Ne.symm hlr⟩).trans hgr⟩

/-- Ordinary tree extension: any prescribed host vertex can be the root. -/
lemma tree_copy_minDegree {W : Type v} [Fintype W] (H : SimpleGraph W)
    (hT : T.IsTree) (r : V) (s₀ : W)
    (hdeg : ∀ s, Fintype.card V - 1 ≤ H.degree s) :
    ∃ f : T.Copy H, f r = s₀ := by
  apply tree_copy_of_fresh H hT r s₀
  intro U hU hcard s hs
  exact fresh_neighbor H U s hs (by have := hdeg s; omega)

/-- Clique-plus-outside extension.  Only outside vertices need a degree bound. -/
lemma tree_copy_clique_outside {W : Type v} [Fintype W] (H : SimpleGraph W)
    (hT : T.IsTree) (r : V) (K : Finset W)
    (hK : H.IsClique (K : Set W)) (hcard : K.card + 1 = Fintype.card V)
    (hdeg : ∀ s, s ∉ K → K.card ≤ H.degree s)
    (s₀ : W) (hs₀ : s₀ ∉ K) :
    ∃ f : T.Copy H, f r = s₀ := by
  apply tree_copy_of_fresh H hT r s₀
  intro U hU hsize s hs
  by_cases hsk : s ∈ K
  · have hinter : (U ∩ K).card < U.card := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
      intro he
      have : s₀ ∈ U ∩ K := he.symm ▸ hU
      exact hs₀ (mem_inter.mp this).2
    have hkfresh : (U ∩ K).card < K.card := by omega
    obtain ⟨t, htk, htu⟩ := exists_mem_notMem_of_card_lt_card hkfresh
    have htnu : t ∉ U := fun ht => htu (mem_inter.mpr ⟨ht, htk⟩)
    exact ⟨t, hK hsk htk (by rintro rfl; exact htnu hs), htnu⟩
  · exact fresh_neighbor H U s hs (by have := hdeg s hsk; omega)

end TreeExtension

section CliqueReservoir

variable {V : Type u} [Fintype V] {T : SimpleGraph V}
variable {W : Type v} [Fintype W] (H : SimpleGraph W)

omit [Fintype W] in
/-- A clique accommodates any graph of the same order, with a specified root. -/
lemma copy_on_clique (r : V) (K : Finset W) (hK : H.IsClique (K : Set W))
    (hcard : K.card = Fintype.card V) (z : W) (hz : z ∈ K) :
    ∃ f : T.Copy H, f r = z ∧ univ.image f = K := by
  obtain ⟨e⟩ : Nonempty (V ↪ K) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hcard.ge)
  let e' : V ↪ K := e.setValue r ⟨z, hz⟩
  let f : T.Copy H :=
    ⟨⟨fun x => (e' x).val, fun {x y} hxy =>
      hK (e' x).property (e' y).property
        (fun he => hxy.ne (e'.injective (Subtype.ext he)))⟩,
      fun x y he => e'.injective (Subtype.ext he)⟩
  refine ⟨f, ?_, ?_⟩
  · change (e' r).val = z
    simp [e']
  · apply Finset.eq_of_subset_of_card_le
    · rintro x hx
      obtain ⟨y, _, rfl⟩ := mem_image.mp hx
      exact (e' y).property
    · rw [card_image_of_injective (f := f) _ f.injective, card_univ, hcard]

/-- A rooted tree copy can be required to cover a small clique through its root. -/
lemma tree_copy_cover_clique (hT : T.IsTree) (r : V) (K : Finset W)
    (hK : H.IsClique (K : Set W)) (hcard : K.card ≤ Fintype.card V)
    (z : W) (hz : z ∈ K)
    (hdeg : ∀ s, Fintype.card V - 1 ≤ H.degree s) :
    ∃ f : T.Copy H, f r = z ∧ K ⊆ univ.image f := by
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases heq : K.card = Fintype.card V
    · obtain ⟨f, hfr, hfK⟩ := copy_on_clique H r K hK heq z hz
      exact ⟨f, hfr, hfK ▸ Finset.Subset.refl K⟩
    · have hlt : K.card < Fintype.card V := lt_of_le_of_ne hcard heq
      have hpos : 0 < K.card := Finset.card_pos.mpr ⟨z, hz⟩
      letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨l, hlr, hl⟩ := exists_leaf_ne hT r
      obtain ⟨p, hlp, hp⟩ := degree_eq_one_iff_existsUnique_adj.mp hl
      have hc : Fintype.card ({l}ᶜ : Set V) + 1 = Fintype.card V := by
        change Fintype.card {x : V // ¬ x = l} + 1 = Fintype.card V
        rw [Fintype.card_subtype_compl]
        simp only [Fintype.card_unique]
        exact Nat.sub_add_cancel Fintype.card_pos
      obtain ⟨g, hgr, hgK⟩ := ih (Fintype.card ({l}ᶜ : Set V)) (by omega)
        (tree_delete_leaf hT hl) (⟨r, Ne.symm hlr⟩ : ({l}ᶜ : Set V))
        (by omega) (fun s => by have := hdeg s; omega) rfl
      let U : Finset W := univ.image g
      have hu (x : ({l}ᶜ : Set V)) : g x ∈ U := mem_image.mpr ⟨x, mem_univ _, rfl⟩
      have huc : U.card = Fintype.card ({l}ᶜ : Set V) := by
        exact (card_image_of_injective (f := g) _ g.injective).trans (card_univ)
      obtain ⟨s, hps, hs⟩ := fresh_neighbor H U (g ⟨p, hlp.ne.symm⟩)
        (hu ⟨p, hlp.ne.symm⟩) (by have := hdeg (g ⟨p, hlp.ne.symm⟩); omega)
      obtain ⟨f, _, hfg⟩ := extend_leaf H hlp hp g s
        (by rintro ⟨x, rfl⟩; exact hs (hu x)) hps.symm
      refine ⟨f, (hfg ⟨r, Ne.symm hlr⟩).trans hgr, ?_⟩
      intro x hx
      obtain ⟨y, _, rfl⟩ := mem_image.mp (hgK hx)
      exact mem_image.mpr ⟨y.val, mem_univ _, hfg y⟩

/-- Failure supplies universal outside vertices, hence a clique of any order
up to the tree order plus one, still meeting the common allowed set. -/
lemma clique_of_universal_extensions (hT : T.IsTree) (r : V)
    (A : Finset W) (z : W) (hz : z ∈ A)
    (hdeg : ∀ s, Fintype.card V - 1 ≤ H.degree s)
    (huniv : ∀ f : T.Copy H, f r ∈ A →
      ∃ s, s ∉ univ.image f ∧ ∀ x, H.Adj s (f x)) :
    ∀ t : ℕ, 1 ≤ t → t ≤ Fintype.card V + 1 →
      ∃ K : Finset W, K.card = t ∧ H.IsClique (K : Set W) ∧ z ∈ K := by
  intro t ht htmax
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction n with
  | zero =>
    exact ⟨{z}, by simp, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨K, hcard, hK, hzK⟩ := ih (by omega) (by omega)
    obtain ⟨f, hfr, hfK⟩ := tree_copy_cover_clique H hT r K hK (by omega) z hzK hdeg
    obtain ⟨s, hs, hsadj⟩ := huniv f (hfr ▸ hz)
    have hsK : s ∉ K := fun h => hs (hfK h)
    refine ⟨insert s K, by simp [hsK, hcard]; omega, ?_, by simp [hzK]⟩
    intro x hx y hy hxy
    simp only [Finset.mem_coe, mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · obtain ⟨v, _, rfl⟩ := mem_image.mp (hfK hy)
      exact hsadj v
    · obtain ⟨v, _, rfl⟩ := mem_image.mp (hfK hx)
      exact (hsadj v).symm
    · exact hK hx hy hxy

end CliqueReservoir

section Swaps

variable {V : Type u} [Fintype V] {T : SimpleGraph V}
variable {W : Type v} (H : SimpleGraph W)

/-- A root-centered star; singleton trees satisfy this predicate as well. -/
def RootStar (T : SimpleGraph V) (r : V) : Prop :=
  ∀ x, x ≠ r → T.Adj r x

lemma nonstar_card (hT : T.IsTree) (r : V) (hstar : ¬ RootStar T r) :
    3 ≤ Fintype.card V := by
  obtain ⟨x, hxr, hnx⟩ : ∃ x, x ≠ r ∧ ¬ T.Adj r x := by
    simpa [RootStar] using hstar
  letI : Nontrivial V := ⟨⟨x, r, hxr⟩⟩
  obtain ⟨y, hy⟩ := (T.degree_pos_iff_exists_adj r).mp
    (hT.isConnected.preconnected.degree_pos_of_nontrivial r)
  have hyr : y ≠ r := hy.ne.symm
  have hyx : y ≠ x := fun h => hnx (h ▸ hy)
  have hc := (Finset.card_le_univ ({r, x, y} : Finset V))
  simpa [hxr, hxr.symm, hyr, hyr.symm, hyx, hyx.symm] using hc

omit [Fintype V] in
/-- A legal one-vertex switch is again a copy, and frees the old image. -/
lemma copy_switch (f : T.Copy H) (v : V) (s : W)
    (hs : s ∉ Set.range f)
    (hadj : ∀ w, T.Adj v w → H.Adj s (f w)) :
    ∃ g : T.Copy H, g v = s ∧ (∀ w, w ≠ v → g w = f w) ∧
      f v ∉ Set.range g := by
  let g : V → W := Function.update f v s
  have hne : ∀ w, f w ≠ s := fun w he => hs ⟨w, he⟩
  have hginj : Function.Injective g := by
    intro x y hxy
    by_cases hx : x = v <;> by_cases hy : y = v
    · exact hx.trans hy.symm
    · have : s = f y := by simpa [g, hx, hy] using hxy
      exact (hne y this.symm).elim
    · have : f x = s := by simpa [g, hx, hy] using hxy
      exact (hne x this).elim
    · exact f.injective (by simpa [g, hx, hy] using hxy)
  refine ⟨⟨⟨g, ?_⟩, hginj⟩, by change g v = s; simp [g], ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x = v
    · subst x
      simpa [g, hxy.ne.symm] using hadj y hxy
    · by_cases hy : y = v
      · subst y
        simpa [g, hxy.ne] using (hadj x hxy.symm).symm
      · simpa [g, hx, hy] using f.toHom.map_rel' hxy
  · intro w hw
    simp [g, hw]
  · rintro ⟨w, hw⟩
    change g w = f v at hw
    by_cases hwv : w = v
    · exact hne v (by simpa [g, hwv] using hw.symm)
    · exact hwv (f.injective (by simpa [g, hwv] using hw))

/-- The root-sensitive local count. This is the sum-ready form of the four
classes in the audited proof. Both counts are over source vertices. -/
lemma component_deficit (hT : T.IsTree) (r : V) (hsize : 2 ≤ Fintype.card V)
    (f : V → W) (X A : Finset W) (s : W)
    (hstar : s ∈ A ∨ ¬ RootStar T r)
    (hblocked : ∀ v, f v ∈ X → (v ≠ r ∨ s ∈ A) →
      ∃ w, T.Adj v w ∧ ¬ H.Adj s (f w)) :
    2 ≤ (univ.filter (fun v => ¬ H.Adj s (f v))).card +
      (univ.filter (fun v => f v ∉ X)).card := by
  let M := univ.filter (fun v => ¬ H.Adj s (f v))
  let Y := univ.filter (fun v => f v ∉ X)
  change 2 ≤ M.card + Y.card
  by_contra! hlt
  by_cases hm : M.Nonempty
  · obtain ⟨v, hv⟩ := hm
    have hmpos : 0 < M.card := card_pos.mpr ⟨v, hv⟩
    have hym : Y = ∅ := card_eq_zero.mp (by omega)
    have hallX (w : V) : f w ∈ X := by
      by_contra hn
      have : w ∈ Y := by simp [Y, hn]
      simp [hym] at this
    have huniq : ∀ w, ¬ H.Adj s (f w) → w = v := by
      intro w hw
      exact card_le_one.mp (by omega : M.card ≤ 1) w (by simp [M, hw]) v hv
    by_cases hlegal : v ≠ r ∨ s ∈ A
    · obtain ⟨w, hvw, hw⟩ := hblocked v (hallX v) hlegal
      exact hvw.ne (huniq w hw).symm
    · have hvr : v = r := by tauto
      have hnA : s ∉ A := by tauto
      obtain ⟨u, hur, hnu⟩ : ∃ u, u ≠ r ∧ ¬ T.Adj r u := by
        simpa [RootStar] using hstar.resolve_left hnA
      obtain ⟨w, huw, hw⟩ := hblocked u (hallX u) (Or.inl hur)
      have hwr : w = r := (huniq w hw).trans hvr
      exact hnu (hwr ▸ huw.symm)
  · have hmempty : M = ∅ := not_nonempty_iff_eq_empty.mp hm
    have hno (v : V) (hv : f v ∈ X) (hlegal : v ≠ r ∨ s ∈ A) : False := by
      obtain ⟨w, _, hw⟩ := hblocked v hv hlegal
      have : w ∈ M := by simp [M, hw]
      simp [hmempty] at this
    by_cases hsA : s ∈ A
    · have hc : Y.card < (univ : Finset V).card := by simp only [card_univ]; omega
      obtain ⟨v, _, hv⟩ := exists_mem_notMem_of_card_lt_card hc
      exact hno v (by simpa [Y] using hv) (Or.inr hsA)
    · have hn : 3 ≤ Fintype.card V := nonstar_card hT r (hstar.resolve_left hsA)
      have hi := card_insert_le r Y
      have hc : (insert r Y).card < (univ : Finset V).card := by
        simp only [card_univ]; omega
      obtain ⟨v, _, hv⟩ := exists_mem_notMem_of_card_lt_card hc
      have hvr : v ≠ r := fun he => hv (by simp [he])
      have hvY : v ∉ Y := fun he => hv (mem_insert_of_mem he)
      exact hno v (by simpa [Y] using hvY) (Or.inl hvr)

end Swaps

/-- A nonempty finite rooted tree. Isolated vertices are allowed. -/
structure RootedTree where
  V : Type u
  finiteV : Fintype V
  graph : SimpleGraph V
  isTree : graph.IsTree
  root : V

attribute [instance] RootedTree.finiteV

namespace RootedTree

noncomputable def order (T : RootedTree) : ℕ := Fintype.card T.V
noncomputable def edges (T : RootedTree) : ℕ := T.order - 1

lemma order_pos (T : RootedTree) : 0 < T.order := Fintype.card_pos_iff.mpr ⟨T.root⟩

lemma edges_add_one (T : RootedTree) : T.edges + 1 = T.order := by
  have := T.order_pos
  simp only [edges]
  omega

lemma edges_eq_card (T : RootedTree) : T.edges = T.graph.edgeFinset.card := by
  have := T.isTree.card_edgeFinset
  have := T.edges_add_one
  change T.edges + 1 = Fintype.card T.V at this
  omega

end RootedTree

section Families

variable {I : Type u} (T : I → RootedTree.{u})

/-- The disjoint union of the component trees, with a standard `SimpleGraph`
interface. Adjacency never joins two different components. -/
def forestGraph : SimpleGraph (Σ i, (T i).V) where
  Adj x y := ∃ (i : I) (a b : (T i).V), x = ⟨i, a⟩ ∧ y = ⟨i, b⟩ ∧ (T i).graph.Adj a b
  symm := by
    rintro x y ⟨i, a, b, rfl, rfl, hab⟩
    exact ⟨i, b, a, rfl, rfl, hab.symm⟩
  loopless := by
    rintro x ⟨i, a, b, hxa, hxb, hab⟩
    exact hab.ne (eq_of_heq (Sigma.mk.inj (hxa.symm.trans hxb)).2)

@[simp] lemma forestGraph_adj_same (i : I) (a b : (T i).V) :
    (forestGraph T).Adj ⟨i, a⟩ ⟨i, b⟩ ↔ (T i).graph.Adj a b := by
  constructor
  · rintro ⟨j, c, d, hac, hbd, hcd⟩
    have hij : i = j := congrArg Sigma.fst hac
    subst j
    have ha : a = c := eq_of_heq (Sigma.mk.inj hac).2
    have hb : b = d := eq_of_heq (Sigma.mk.inj hbd).2
    simpa [ha, hb] using hcd
  · exact fun hab => ⟨i, a, b, rfl, rfl, hab⟩

lemma forestGraph_neighbor (i : I) (a : (T i).V) (y : Σ j, (T j).V) :
    (forestGraph T).Adj ⟨i, a⟩ y ↔
      ∃ b : (T i).V, y = ⟨i, b⟩ ∧ (T i).graph.Adj a b := by
  constructor
  · rintro ⟨j, c, d, hac, rfl, hcd⟩
    have hij : i = j := congrArg Sigma.fst hac
    subst j
    have ha : a = c := eq_of_heq (Sigma.mk.inj hac).2
    subst c
    exact ⟨d, rfl, hcd⟩
  · rintro ⟨b, rfl, hab⟩
    exact (forestGraph_adj_same T i a b).mpr hab

/-- Copies satisfying the one-mark-per-component condition. -/
def Marked {W : Type v} {H : SimpleGraph W} (f : (forestGraph T).Copy H)
    (A : Finset W) : Prop := ∀ i, f ⟨i, (T i).root⟩ ∈ A

/-- All vertex images avoid a reserved set. -/
def Avoids {V' : Type*} {W : Type v} {F : SimpleGraph V'} {H : SimpleGraph W}
    (f : F.Copy H) (D : Finset W) : Prop := ∀ x, f x ∉ D

variable [Fintype I]

noncomputable def totalOrder : ℕ := ∑ i, (T i).order
noncomputable def totalEdges : ℕ := ∑ i, (T i).edges

lemma totalOrder_eq : totalOrder T = totalEdges T + Fintype.card I := by
  simp only [totalOrder, totalEdges, ← RootedTree.edges_add_one, sum_add_distrib,
    sum_const, card_univ, smul_eq_mul, mul_one]

lemma card_vertices : Fintype.card (Σ i, (T i).V) = totalOrder T :=
  Fintype.card_sigma

/-- Restrict a union copy to one component. -/
def componentCopy {W : Type v} {H : SimpleGraph W} (f : (forestGraph T).Copy H)
    (i : I) : (T i).graph.Copy H :=
  ⟨⟨fun x => f ⟨i, x⟩, fun h => f.toHom.map_rel' ((forestGraph_adj_same T i _ _).mpr h)⟩,
    fun _ _ h => eq_of_heq (Sigma.mk.inj (f.injective h)).2⟩

/-- Counting a predicate on the union image is a sum of its component counts. -/
lemma card_filter_image {W : Type v} (f : (Σ i, (T i).V) ↪ W) (P : W → Prop) [DecidablePred P] :
    ((univ.image f).filter P).card =
      ∑ i, (univ.filter (fun x : (T i).V => P (f ⟨i, x⟩))).card := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ f.injective]
  simp only [Finset.card_filter, Fintype.sum_sigma]

/-- A blocked global switch gives a missed neighbor in the component. -/
lemma blocked_switch {W : Type v} {H : SimpleGraph W} (A K X : Finset W)
    (hcover : ∀ g : (forestGraph T).Copy H,
      Marked T g A → Avoids g K → X ⊆ univ.image g)
    (f : (forestGraph T).Copy H) (hfA : Marked T f A) (hfK : Avoids f K)
    (s : W) (hsK : s ∉ K) (hsf : s ∉ univ.image f)
    (i : I) (v : (T i).V) (hvX : f ⟨i, v⟩ ∈ X)
    (hlegal : v ≠ (T i).root ∨ s ∈ A) :
    ∃ w, (T i).graph.Adj v w ∧ ¬ H.Adj s (f ⟨i, w⟩) := by
  by_contra! hn
  obtain ⟨g, hgv, hgf, hmiss⟩ := copy_switch H f ⟨i, v⟩ s
    (by rintro ⟨x, rfl⟩; exact hsf (mem_image.mpr ⟨x, mem_univ _, rfl⟩))
    (by
      intro y hy
      obtain ⟨w, rfl, hvw⟩ := (forestGraph_neighbor T i v y).mp hy
      exact hn w hvw)
  have hgA : Marked T g A := by
    intro j
    by_cases heq : (⟨j, (T j).root⟩ : Σ j, (T j).V) = ⟨i, v⟩
    · have hji : j = i := congrArg Sigma.fst heq
      subst j
      have hrv : (T i).root = v := eq_of_heq (Sigma.mk.inj heq).2
      have hsA : s ∈ A := hlegal.resolve_left (by simp [hrv])
      simpa [heq, hgv] using hsA
    · rw [hgf _ heq]
      exact hfA j
  have hgK : Avoids g K := by
    intro x
    by_cases heq : x = ⟨i, v⟩
    · simpa [heq, hgv] using hsK
    · rw [hgf _ heq]
      exact hfK x
  obtain ⟨x, _, hx⟩ := mem_image.mp (hcover g hgA hgK hvX)
  exact hmiss ⟨x, hx⟩

/-- The residual-degree calculation, with the four classes summed implicitly.
The set `X` has one more vertex than the number of remaining forest edges. -/
lemma residual_degree {W : Type v} [Fintype W] (H : SimpleGraph W)
    (A K X : Finset W)
    (hcover : ∀ g : (forestGraph T).Copy H,
      Marked T g A → Avoids g K → X ⊆ univ.image g)
    (f : (forestGraph T).Copy H) (hfA : Marked T f A) (hfK : Avoids f K)
    (hsize : ∀ i, 2 ≤ (T i).order)
    (a : ℕ) (hdeg : ∀ s, a + totalEdges T ≤ H.degree s)
    (hXcard : X.card = totalEdges T + 1)
    (s : W) (hsK : s ∉ K) (hsf : s ∉ univ.image f)
    (hstar : ∀ i, s ∈ A ∨ ¬ RootStar (T i).graph (T i).root) :
    a + 1 ≤ (H.neighborFinset s \ univ.image f).card := by
  let B : Finset W := univ.image f
  have hlocal (i : I) : 2 ≤
      (univ.filter (fun v : (T i).V => ¬ H.Adj s (f ⟨i, v⟩))).card +
      (univ.filter (fun v : (T i).V => f ⟨i, v⟩ ∉ X)).card :=
    component_deficit H (T i).isTree (T i).root (hsize i) _ X A s (hstar i)
      (blocked_switch T A K X hcover f hfA hfK s hsK hsf i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) => hlocal i)
  have hM : (B \ H.neighborFinset s).card =
      ∑ i, (univ.filter (fun v : (T i).V => ¬ H.Adj s (f ⟨i, v⟩))).card := by
    simpa only [B, Finset.sdiff_eq_filter, mem_neighborFinset, Copy.toEmbedding, Function.Embedding.coeFn_mk] using
      card_filter_image T f.toEmbedding (fun x => ¬ H.Adj s x)
  have hY : (B \ X).card =
      ∑ i, (univ.filter (fun v : (T i).V => f ⟨i, v⟩ ∉ X)).card := by
    simpa only [B, Finset.sdiff_eq_filter, Copy.toEmbedding, Function.Embedding.coeFn_mk] using card_filter_image T f.toEmbedding (· ∉ X)
  simp only [sum_add_distrib, sum_const, card_univ, smul_eq_mul] at hsum
  rw [← hM, ← hY] at hsum
  have hB : B.card = totalEdges T + Fintype.card I := by
    dsimp only [B]
    rw [Finset.card_image_of_injective (f := f) _ f.injective, card_univ,
      card_vertices, totalOrder_eq]
  have hXsub : X ⊆ B := hcover f hfA hfK
  have hYX := card_sdiff_add_card_eq_card hXsub
  have hBN := card_sdiff_add_card_inter B (H.neighborFinset s)
  have hNB := card_sdiff_add_card_inter (H.neighborFinset s) B
  rw [inter_comm B (H.neighborFinset s)] at hBN
  rw [H.card_neighborFinset_eq_degree] at hNB
  have hd := hdeg s
  change a + 1 ≤ (H.neighborFinset s \ B).card
  omega

end Families

section FinalTreeCopies

variable {V : Type u} [Fintype V] {T : SimpleGraph V}
variable {W : Type v} [Fintype W] (H : SimpleGraph W)

omit [Fintype V] in
lemma rootStar_edge (hT : T.IsAcyclic) (r : V) (hstar : RootStar T r)
    {x y : V} (hxy : T.Adj x y) : x = r ∨ y = r := by
  by_contra! hn
  let p : T.Walk r y := .cons (hstar x hn.1) (.cons hxy .nil)
  have hp : p.IsPath := by
    simp [p, Walk.cons_isPath_iff, hxy.ne, hn.1.symm, hn.2.symm]
  have he := hT.path_unique ⟨p, hp⟩ (Path.singleton (hstar y hn.2))
  have hl := congrArg (fun q : T.Path r y => q.val.length) he
  simp [p, Path.singleton] at hl

/-- A root-centered star only needs a degree bound at its chosen center. -/
lemma rootstar_copy (hT : T.IsTree) (r : V) (hstar : RootStar T r) (s : W)
    (hdeg : Fintype.card V - 1 ≤ H.degree s) :
    ∃ f : T.Copy H, f r = s := by
  have hc : Fintype.card ({r}ᶜ : Set V) = Fintype.card V - 1 := by
    change Fintype.card {x : V // ¬ x = r} = _
    rw [Fintype.card_subtype_compl]
    simp
  obtain ⟨e⟩ : Nonempty (({r}ᶜ : Set V) ↪ H.neighborSet s) :=
    Function.Embedding.nonempty_of_card_le (by
      rw [hc, H.card_neighborSet_eq_degree]
      exact hdeg)
  let f : V → W := fun x => if hx : x = r then s else (e ⟨x, hx⟩).val
  have he (x : ({r}ᶜ : Set V)) : H.Adj s (e x).val := (e x).property
  refine ⟨⟨⟨f, ?_⟩, ?_⟩, by change f r = s; simp [f]⟩
  · intro x y hxy
    rcases rootStar_edge hT.IsAcyclic r hstar hxy with rfl | rfl
    · simpa [f, hxy.ne.symm] using he ⟨y, hxy.ne.symm⟩
    · simpa [f, hxy.ne] using (he ⟨x, hxy.ne⟩).symm
  · intro x y hxy
    by_cases hx : x = r <;> by_cases hy : y = r
    · exact hx.trans hy.symm
    · have hh : s = (e ⟨y, hy⟩).val := by simpa [f, hx, hy] using hxy
      exact ((he ⟨y, hy⟩).ne hh).elim
    · have hh : (e ⟨x, hx⟩).val = s := by simpa [f, hx, hy] using hxy
      exact ((he ⟨x, hx⟩).ne hh.symm).elim
    · have hh : (e ⟨x, hx⟩).val = (e ⟨y, hy⟩).val := by simpa [f, hx, hy] using hxy
      exact congrArg Subtype.val (e.injective (Subtype.ext hh))

omit [Fintype W] in
/-- Fix a leaf-deleted rooted tree on a clique. The designated parent image
(not an arbitrary clique vertex) can then be used for every leaf extension. -/
lemma leaf_reservoir (hT : T.IsTree) (r : V) (hsize : 2 ≤ Fintype.card V)
    (K : Finset W) (hK : H.IsClique (K : Set W))
    (hcard : K.card + 1 = Fintype.card V) (z : W) (hz : z ∈ K) :
    ∃ x ∈ K, ∀ w, w ∉ K → H.Adj x w →
      ∃ f : T.Copy H, f r = z ∧ ∀ v, f v ∈ insert w K := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨l, hlr, hl⟩ := exists_leaf_ne hT r
  obtain ⟨p, hlp, hp⟩ := degree_eq_one_iff_existsUnique_adj.mp hl
  have hc : Fintype.card ({l}ᶜ : Set V) = K.card := by
    change Fintype.card {x : V // ¬ x = l} = _
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_unique]
    omega
  obtain ⟨g, hgr, hgK⟩ := copy_on_clique (T := T.induce {l}ᶜ) H
    ⟨r, Ne.symm hlr⟩ K hK hc.symm z hz
  have hgmem (v : ({l}ᶜ : Set V)) : g v ∈ K :=
    hgK ▸ mem_image.mpr ⟨v, mem_univ _, rfl⟩
  refine ⟨g ⟨p, hlp.ne.symm⟩, hgmem _, ?_⟩
  intro w hwK hxw
  obtain ⟨f, hfl, hfg⟩ := extend_leaf H hlp hp g w
    (by rintro ⟨v, rfl⟩; exact hwK (hgmem v)) hxw.symm
  refine ⟨f, (hfg ⟨r, Ne.symm hlr⟩).trans hgr, ?_⟩
  intro v
  by_cases hv : v = l
  · simp [hv, hfl]
  · rw [hfg ⟨v, hv⟩]
    exact mem_insert_of_mem (hgmem _)

end FinalTreeCopies

section ComponentInsertion

variable {I : Type u} (T : I → RootedTree.{u}) (i₀ : I)

/-- The family after deleting one component. -/
def restFamily : {i : I // i ≠ i₀} → RootedTree.{u} := fun i => T i.val

private noncomputable def joinFun {W : Type v} (f : (T i₀).V → W)
    (g : (Σ i, (restFamily T i₀ i).V) → W) : (Σ i, (T i).V) → W :=
  fun ⟨i, x⟩ => if h : i = i₀ then f (h ▸ x) else g ⟨⟨i, h⟩, x⟩

@[simp] private lemma joinFun_same {W : Type v} (f : (T i₀).V → W)
    (g : (Σ i, (restFamily T i₀ i).V) → W) (x : (T i₀).V) :
    joinFun T i₀ f g ⟨i₀, x⟩ = f x := by simp [joinFun]

@[simp] private lemma joinFun_other {W : Type v} (f : (T i₀).V → W)
    (g : (Σ i, (restFamily T i₀ i).V) → W) (i : {i : I // i ≠ i₀})
    (x : (T i.val).V) : joinFun T i₀ f g ⟨i.val, x⟩ = g ⟨i, x⟩ := by
  simp [joinFun, i.property]

lemma join_copies {W : Type v} {H : SimpleGraph W}
    (f : (T i₀).graph.Copy H) (g : (forestGraph (restFamily T i₀)).Copy H)
    (hdis : ∀ x y, f x ≠ g y) :
    ∃ h : (forestGraph T).Copy H,
      (∀ x, h ⟨i₀, x⟩ = f x) ∧
      (∀ (i : {i : I // i ≠ i₀}) (x : (T i.val).V), h ⟨i.val, x⟩ = g ⟨i, x⟩) := by
  let j := joinFun T i₀ f g
  have hj₀ : ∀ x, j ⟨i₀, x⟩ = f x := joinFun_same T i₀ f g
  have hjr : ∀ (i : {i : I // i ≠ i₀}) (x : (T i.val).V), j ⟨i.val, x⟩ = g ⟨i, x⟩ :=
    joinFun_other T i₀ f g
  refine ⟨⟨⟨j, ?_⟩, ?_⟩, hj₀, hjr⟩
  · rintro _ _ ⟨i, x, y, rfl, rfl, hxy⟩
    by_cases hi : i = i₀
    · subst i
      rw [hj₀, hj₀]
      exact f.toHom.map_rel' hxy
    · rw [hjr ⟨i, hi⟩, hjr ⟨i, hi⟩]
      exact g.toHom.map_rel' ((forestGraph_adj_same (restFamily T i₀) ⟨i, hi⟩ x y).mpr hxy)
  · rintro ⟨i, x⟩ ⟨k, y⟩ hxy
    change j ⟨i, x⟩ = j ⟨k, y⟩ at hxy
    by_cases hi : i = i₀ <;> by_cases hk : k = i₀
    · subst i; subst k
      rw [hj₀, hj₀] at hxy
      exact congrArg (Sigma.mk i₀) (f.injective hxy)
    · subst i
      rw [hj₀, hjr ⟨k, hk⟩] at hxy
      exact (hdis _ _ hxy).elim
    · subst k
      rw [hjr ⟨i, hi⟩, hj₀] at hxy
      exact (hdis _ _ hxy.symm).elim
    · rw [hjr ⟨i, hi⟩, hjr ⟨k, hk⟩] at hxy
      have he := g.injective hxy
      exact congrArg (fun z : Σ i, (restFamily T i₀ i).V =>
        (⟨z.1.val, z.2⟩ : Σ i, (T i).V)) he

lemma join_marked {W : Type v} {H : SimpleGraph W} (A : Finset W)
    (f : (T i₀).graph.Copy H) (hf : f (T i₀).root ∈ A)
    (g : (forestGraph (restFamily T i₀)).Copy H) (hg : Marked (restFamily T i₀) g A)
    (hdis : ∀ x y, f x ≠ g y) :
    ∃ h : (forestGraph T).Copy H, Marked T h A := by
  obtain ⟨h, hh₀, hhr⟩ := join_copies T i₀ f g hdis
  refine ⟨h, ?_⟩
  intro i
  by_cases hi : i = i₀
  · subst i
    rw [hh₀]
    exact hf
  · rw [hhr ⟨i, hi⟩]
    exact hg ⟨i, hi⟩

variable [Fintype I]

lemma sum_except (b : I → ℕ) :
    b i₀ + (∑ i : {i : I // i ≠ i₀}, b i.val) = ∑ i, b i := by
  rw [← Finset.sum_subtype (univ.erase i₀) (by simp)]
  exact (add_comm _ _).trans (sum_erase_add univ b (mem_univ i₀))

lemma totalOrder_except : totalOrder T = (T i₀).order + totalOrder (restFamily T i₀) :=
  (sum_except i₀ (fun i => (T i).order)).symm

lemma totalEdges_except : totalEdges T = (T i₀).edges + totalEdges (restFamily T i₀) :=
  (sum_except i₀ (fun i => (T i).edges)).symm

lemma card_rest_lt : Fintype.card {i : I // i ≠ i₀} < Fintype.card I :=
  Fintype.card_subtype_lt (x := i₀) (by simp)

end ComponentInsertion

section AllowedDeletion

variable {W : Type v} [Fintype W]

/-- The common allowed set in the vertex-deleted host. -/
noncomputable def allowedAfter (A D : Finset W) : Finset ↑((D : Set W)ᶜ) :=
  univ.filter (fun x => x.val ∈ A)

@[simp] lemma mem_allowedAfter (A D : Finset W) (x : ↑((D : Set W)ᶜ)) :
    x ∈ allowedAfter A D ↔ x.val ∈ A := by simp [allowedAfter]

lemma card_allowedAfter (A D : Finset W) : (allowedAfter A D).card = (A \ D).card := by
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    exact mem_sdiff.mpr ⟨(mem_allowedAfter A D x).mp hx, x.property⟩
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro x hx
    refine ⟨⟨x, (mem_sdiff.mp hx).2⟩, ?_, rfl⟩
    exact (mem_allowedAfter A D _).mpr (mem_sdiff.mp hx).1

end AllowedDeletion

section InductionSteps

variable {I : Type u} [Fintype I] (T : I → RootedTree.{u}) (i₀ : I)
variable {W : Type v} [Fintype W] (H : SimpleGraph W) (A : Finset W)

/-- The induction step for an isolated marked component: use an unused member
of the common list after placing the other components. -/
lemma isolated_step (hi₀ : (T i₀).order = 1)
    (hdeg : ∀ s, totalEdges T ≤ H.degree s) (hA : totalOrder T ≤ A.card)
    (hrest : ∀ D : Finset W,
      (∀ s, s ∉ D → totalEdges (restFamily T i₀) ≤ (H.neighborFinset s \ D).card) →
      totalOrder (restFamily T i₀) ≤ (A \ D).card →
      ∃ g : (forestGraph (restFamily T i₀)).Copy H,
        Marked (restFamily T i₀) g A ∧ Avoids g D) :
    ∃ f : (forestGraph T).Copy H, Marked T f A := by
  have he := totalEdges_except T i₀
  have ho := totalOrder_except T i₀
  obtain ⟨g, hgA, _⟩ := hrest ∅
    (by intro s _; simpa using (show totalEdges (restFamily T i₀) ≤ H.degree s by
      have := hdeg s; omega))
    (by simpa using (show totalOrder (restFamily T i₀) ≤ A.card by omega))
  have hB : (univ.image g).card = totalOrder (restFamily T i₀) := by
    rw [card_image_of_injective (f := g) _ g.injective, card_univ, card_vertices]
  obtain ⟨s, hsA, hsg⟩ := exists_mem_notMem_of_card_lt_card
    (s := univ.image g) (t := A) (by omega)
  obtain ⟨f, hfr⟩ := tree_copy_minDegree H (T i₀).isTree (T i₀).root s
    (by intro x; change (T i₀).order - 1 ≤ _; simp [hi₀])
  letI : Subsingleton (T i₀).V := Fintype.card_le_one_iff_subsingleton.mp (by
    change (T i₀).order ≤ 1; omega)
  apply join_marked T i₀ A f (hfr ▸ hsA) g hgA
  intro x y hxy
  have hxs : f x = s := (congrArg f (Subsingleton.elim x (T i₀).root)).trans hfr
  exact hsg (mem_image.mpr ⟨y, mem_univ _, hxy.symm.trans hxs⟩)

/-- The nontrivial-component step of CL. A root-centered star is selected
first when one is present; otherwise all swaps can preserve the roots. -/
lemma nontrivial_step (hsize : ∀ i, 2 ≤ (T i).order)
    (hpriority : RootStar (T i₀).graph (T i₀).root ∨
      ∀ i, ¬ RootStar (T i).graph (T i).root)
    (hdeg : ∀ s, totalEdges T ≤ H.degree s) (hA : totalOrder T ≤ A.card)
    (hrest : ∀ D : Finset W,
      (∀ s, s ∉ D → totalEdges (restFamily T i₀) ≤ (H.neighborFinset s \ D).card) →
      totalOrder (restFamily T i₀) ≤ (A \ D).card →
      ∃ g : (forestGraph (restFamily T i₀)).Copy H,
        Marked (restFamily T i₀) g A ∧ Avoids g D) :
    ∃ f : (forestGraph T).Copy H, Marked T f A := by
  let R := restFamily T i₀
  let a := (T i₀).edges
  let b := totalEdges R
  have he : totalEdges T = a + b := totalEdges_except T i₀
  have ho : totalOrder T = a + 1 + totalOrder R := by
    rw [totalOrder_except T i₀, ← (T i₀).edges_add_one]
  have ha : 1 ≤ a := by have := hsize i₀; have := (T i₀).edges_add_one; omega
  have htreecard : a + 1 = Fintype.card (T i₀).V := (T i₀).edges_add_one
  have htreeDeg (s : W) : Fintype.card (T i₀).V - 1 ≤ H.degree s := by
    have := hdeg s; omega
  obtain ⟨z, hzA⟩ : A.Nonempty := card_pos.mp (by omega)
  by_contra hfail
  -- No rooted first-component copy can have all outside vertices miss it.
  have huniv (f : (T i₀).graph.Copy H) (hfr : f (T i₀).root ∈ A) :
      ∃ s, s ∉ univ.image f ∧ ∀ x, H.Adj s (f x) := by
    by_contra! hn
    let D := univ.image f
    have hD : D.card = a + 1 := by
      rw [Finset.card_image_of_injective (f := f) _ f.injective, card_univ]
      exact htreecard.symm
    obtain ⟨g, hgA, hgD⟩ := hrest D
      (by
        intro s hsD
        obtain ⟨v, hv⟩ := hn s hsD
        have hbnd := degree_lt_remaining_add_of_miss H D s (f v)
          (mem_image.mpr ⟨v, mem_univ _, rfl⟩) hv
        have hd := hdeg s
        change b ≤ _
        omega)
      (by have hsub := Finset.le_card_sdiff D A; change totalOrder R ≤ _; omega)
    apply hfail
    apply join_marked T i₀ A f hfr g hgA
    intro x y hxy
    exact hgD y (hxy ▸ mem_image.mpr ⟨x, mem_univ _, rfl⟩)
  obtain ⟨K, hKcard, hK, hzK⟩ := clique_of_universal_extensions H (T i₀).isTree
    (T i₀).root A z hzA htreeDeg huniv a ha (by omega)
  obtain ⟨x, hxK, hleaf⟩ := leaf_reservoir H (T i₀).isTree (T i₀).root
    (hsize i₀) K hK (by omega) z hzK
  have hNX : b + 1 ≤ (H.neighborFinset x \ K).card := by
    have hbnd := degree_lt_remaining_add_of_miss H K x x hxK H.irrefl
    have hd := hdeg x
    omega
  obtain ⟨X, hX, hXcard⟩ := exists_subset_card_eq hNX
  -- Embed the remainder outside the reserved clique.
  obtain ⟨g, hgA, hgK⟩ := hrest K
    (by
      intro s _
      have hbnd := degree_le_remaining_add H K s
      have hd := hdeg s
      change b ≤ _
      omega)
    (by have hsub := Finset.le_card_sdiff K A; change totalOrder R ≤ _; omega)
  -- Every such placement covers X; otherwise the reserved leaf finishes F.
  have hcover : ∀ g' : (forestGraph R).Copy H,
      Marked R g' A → Avoids g' K → X ⊆ univ.image g' := by
    intro g' hg'A hg'K w hwX
    by_contra hwg'
    have hw := mem_sdiff.mp (hX hwX)
    obtain ⟨f, hfr, hfmem⟩ := hleaf w hw.2 (by simpa using hw.1)
    apply hfail
    apply join_marked T i₀ A f (hfr ▸ hzA) g' hg'A
    intro v y hvy
    rcases mem_insert.mp (hfmem v) with hvw | hvK
    · exact hwg' (mem_image.mpr ⟨y, mem_univ _, hvy.symm.trans hvw⟩)
    · exact hg'K y (hvy ▸ hvK)
  let B := univ.image g
  have hB : B.card = totalOrder R := by
    rw [Finset.card_image_of_injective (f := g) _ g.injective, card_univ, card_vertices]
  have hKB : Disjoint K B := by
    apply Finset.disjoint_left.mpr
    intro y hyK hyB
    obtain ⟨v, _, rfl⟩ := mem_image.mp hyB
    exact hgK v hyK
  have hfree : (K ∪ B).card < A.card := by
    have := card_union_le K B
    omega
  obtain ⟨s₀, hs₀A, hs₀⟩ := exists_mem_notMem_of_card_lt_card hfree
  have hs₀K : s₀ ∉ K := fun h => hs₀ (mem_union_left B h)
  have hs₀B : s₀ ∉ B := fun h => hs₀ (mem_union_right K h)
  let J := H.induce (B : Set W)ᶜ
  let sJ : ↑((B : Set W)ᶜ) := ⟨s₀, hs₀B⟩
  have hRsize : ∀ i, 2 ≤ (R i).order := fun i => hsize i.val
  have hdegree (s : W) (hsK : s ∉ K) (hsB : s ∉ B)
      (hstar : ∀ i, s ∈ A ∨ ¬ RootStar (R i).graph (R i).root) :
      a + 1 ≤ (H.neighborFinset s \ B).card :=
    residual_degree R H A K X hcover g hgA hgK hRsize a
      (by intro v; have := hdeg v; omega) hXcard s hsK hsB hstar
  have finish (f : (T i₀).graph.Copy J) (hfr : f (T i₀).root = sJ) : False := by
    let f' := (Copy.induce H (B : Set W)ᶜ).comp f
    have hfr' : f' (T i₀).root = s₀ := congrArg Subtype.val hfr
    apply hfail
    apply join_marked T i₀ A f' (hfr' ▸ hs₀A) g hgA
    intro v y hvy
    have hv : f' v ∉ B := (f v).property
    exact hv (hvy ▸ mem_image.mpr ⟨y, mem_univ _, rfl⟩)
  by_cases hstar₀ : RootStar (T i₀).graph (T i₀).root
  · have hd : Fintype.card (T i₀).V - 1 ≤ J.degree sJ := by
      have hbnd := hdegree s₀ hs₀K hs₀B (fun _ => Or.inl hs₀A)
      change _ ≤ (H.induce (B : Set W)ᶜ).degree sJ
      rw [degree_induce_compl H B]
      change _ ≤ (H.neighborFinset s₀ \ B).card
      omega
    obtain ⟨f, hfr⟩ := rootstar_copy J (T i₀).isTree (T i₀).root hstar₀ sJ hd
    exact finish f hfr
  · have hnstar : ∀ i, ¬ RootStar (T i).graph (T i).root :=
      hpriority.resolve_left hstar₀
    let KJ := allowedAfter K B
    have hKJcard : KJ.card = a := by
      rw [card_allowedAfter, Finset.sdiff_eq_self_iff_disjoint.mpr hKB, hKcard]
    have hKJ : J.IsClique (KJ : Set ↑((B : Set W)ᶜ)) := by
      intro v hv w hw hvw
      exact hK ((mem_allowedAfter K B v).mp hv) ((mem_allowedAfter K B w).mp hw)
        (fun heq => hvw (Subtype.ext heq))
    have hdJ (s : ↑((B : Set W)ᶜ)) (hsKJ : s ∉ KJ) : KJ.card ≤ J.degree s := by
      have hsK : s.val ∉ K := fun h => hsKJ ((mem_allowedAfter K B s).mpr h)
      have hbnd := hdegree s.val hsK s.property (fun i => Or.inr (hnstar i.val))
      change _ ≤ (H.induce (B : Set W)ᶜ).degree s
      rw [degree_induce_compl H B, hKJcard]
      omega
    have hsJK : sJ ∉ KJ := fun h => hs₀K ((mem_allowedAfter K B sJ).mp h)
    obtain ⟨f, hfr⟩ := tree_copy_clique_outside J (T i₀).isTree (T i₀).root KJ hKJ
      (by omega) hdJ sJ hsJK
    exact finish f hfr

end InductionSteps

/-- **CL for a finite family of rooted tree components.** The edge threshold
is the sum of their edge counts and the common-list threshold is their total
order. Singleton components and the empty family are included. -/
theorem common_list_family {I : Type u} [Fintype I] (T : I → RootedTree.{u})
    {W : Type v} [Fintype W] (H : SimpleGraph W) (A : Finset W)
    (hdeg : ∀ s, totalEdges T ≤ H.degree s) (hA : totalOrder T ≤ A.card) :
    ∃ f : (forestGraph T).Copy H, Marked T f A := by
  induction hn : Fintype.card I using Nat.strong_induction_on generalizing I W with
  | h n ih =>
    by_cases hI : IsEmpty I
    · letI := hI
      obtain ⟨f⟩ := (SimpleGraph.IsContained.of_isEmpty : (forestGraph T).IsContained H)
      exact ⟨f, fun i => isEmptyElim i⟩
    · haveI : Nonempty I := not_isEmpty_iff.mp hI
      -- Apply the smaller-family theorem in an arbitrary vertex-deleted host.
      have hrest (i₀ : I) (D : Finset W)
          (hd : ∀ s, s ∉ D → totalEdges (restFamily T i₀) ≤ (H.neighborFinset s \ D).card)
          (hlist : totalOrder (restFamily T i₀) ≤ (A \ D).card) :
          ∃ g : (forestGraph (restFamily T i₀)).Copy H,
            Marked (restFamily T i₀) g A ∧ Avoids g D := by
        have hlt : Fintype.card {i : I // i ≠ i₀} < n := by
          have := card_rest_lt i₀
          omega
        obtain ⟨f, hf⟩ := ih _ hlt (restFamily T i₀) (H.induce (D : Set W)ᶜ)
          (allowedAfter A D)
          (by intro s; rw [degree_induce_compl H D]; exact hd s.val s.property)
          (by rw [card_allowedAfter]; exact hlist) rfl
        let g := (Copy.induce H (D : Set W)ᶜ).comp f
        refine ⟨g, ?_, ?_⟩
        · intro i
          exact (mem_allowedAfter A D (f ⟨i, (restFamily T i₀ i).root⟩)).mp (hf i)
        · intro x
          exact (f x).property
      by_cases hiso : ∃ i, (T i).order = 1
      · obtain ⟨i₀, hi₀⟩ := hiso
        exact isolated_step T i₀ H A hi₀ hdeg hA (hrest i₀)
      · have hsize (i : I) : 2 ≤ (T i).order := by
          have hp := (T i).order_pos
          have hn : (T i).order ≠ 1 := fun h => hiso ⟨i, h⟩
          omega
        by_cases hstar : ∃ i, RootStar (T i).graph (T i).root
        · obtain ⟨i₀, hi₀⟩ := hstar
          exact nontrivial_step T i₀ H A hsize (Or.inl hi₀) hdeg hA (hrest i₀)
        · obtain ⟨i₀⟩ := ‹Nonempty I›
          exact nontrivial_step T i₀ H A hsize
            (Or.inr (fun i hi => hstar ⟨i, hi⟩)) hdeg hA (hrest i₀)

section StandardForestInterface

/-- The degree in a disjoint union is the degree in the component. -/
lemma forestGraph_degree {I : Type u} [Fintype I] (T : I → RootedTree.{u})
    (i : I) (x : (T i).V) :
    (forestGraph T).degree ⟨i, x⟩ = (T i).graph.degree x := by
  let f : (T i).graph.neighborSet x → (forestGraph T).neighborSet ⟨i, x⟩ :=
    fun y => ⟨⟨i, y.val⟩, (forestGraph_adj_same T i x y.val).mpr y.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro y z hyz
      apply Subtype.ext
      exact eq_of_heq (Sigma.mk.inj (congrArg Subtype.val hyz)).2
    · intro y
      obtain ⟨z, hyz, hxz⟩ := (forestGraph_neighbor T i x y.val).mp y.property
      refine ⟨⟨z, hxz⟩, ?_⟩
      exact Subtype.ext hyz.symm
  have hc := Fintype.card_of_bijective hf
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using hc.symm

/-- The numerical threshold used for tree families is exactly the ordinary
number of edges of their disjoint-union graph. -/
lemma forestGraph_edges {I : Type u} [Fintype I] (T : I → RootedTree.{u}) :
    (forestGraph T).edgeFinset.card = totalEdges T := by
  have hs := (forestGraph T).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sigma] at hs
  have he : (∑ i, ∑ x : (T i).V, (forestGraph T).degree ⟨i, x⟩) = 2 * totalEdges T := by
    calc
      _ = ∑ i, 2 * (T i).edges := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [forestGraph_degree]
        rw [(T i).graph.sum_degrees_eq_twice_card_edges, ← (T i).edges_eq_card]
      _ = _ := (Finset.mul_sum _ _ _).symm
  omega

variable {V : Type u} [Fintype V] (F : SimpleGraph V) (hF : F.IsAcyclic)
    (root : (C : F.ConnectedComponent) → C)

/-- The conventional connected components of an acyclic graph, with the
specified roots, form a finite rooted-tree family. -/
noncomputable def componentFamily : F.ConnectedComponent → RootedTree.{u} := fun C =>
  { V := C
    finiteV := inferInstance
    graph := C.toSimpleGraph
    isTree := hF.isTree_connectedComponent C
    root := root C }

/-- The component-family graph is isomorphic to the original forest. -/
noncomputable def componentUnionIso : forestGraph (componentFamily F hF root) ≃g F where
  toEquiv := Equiv.sigmaFiberEquiv F.connectedComponentMk
  map_rel_iff' := by
    intro x y
    change F.Adj x.2.val y.2.val ↔ (forestGraph (componentFamily F hF root)).Adj x y
    constructor
    · intro hxy
      rcases x with ⟨C, x, hx⟩
      rcases y with ⟨D, y, hy⟩
      have hCD : C = D := hx.symm.trans ((ConnectedComponent.sound hxy.reachable).trans hy)
      cases hCD
      exact ⟨C, ⟨x, hx⟩, ⟨y, hy⟩, rfl, rfl, hxy⟩
    · rintro ⟨C, x, y, rfl, rfl, hxy⟩
      exact hxy

lemma componentFamily_order : totalOrder (componentFamily F hF root) = Fintype.card V :=
  (card_vertices (componentFamily F hF root)).symm.trans
    (componentUnionIso F hF root).card_eq

lemma componentFamily_edges : totalEdges (componentFamily F hF root) = F.edgeFinset.card :=
  (forestGraph_edges (componentFamily F hF root)).symm.trans
    (componentUnionIso F hF root).card_edgeFinset_eq

include hF

/-- **Common-list marked-forest theorem CL**, for standard finite simple graphs.
There is one specified root in each connected component. The embedding is an
injective homomorphism; all roots land in the *same* allowed set `A`. -/
theorem common_list_forest {W : Type v} [Fintype W] (H : SimpleGraph W) (A : Finset W)
    (hdeg : ∀ s, F.edgeFinset.card ≤ H.degree s) (hA : Fintype.card V ≤ A.card) :
    ∃ f : F.Copy H, ∀ C, f (root C).val ∈ A := by
  obtain ⟨g, hg⟩ := common_list_family (componentFamily F hF root) H A
    (by rw [componentFamily_edges]; exact hdeg)
    (by rw [componentFamily_order]; exact hA)
  let e := componentUnionIso F hF root
  refine ⟨g.comp e.symm.toCopy, ?_⟩
  intro C
  have hr : e.symm (root C).val = ⟨C, root C⟩ :=
    e.toEquiv.symm_apply_apply ⟨C, root C⟩
  change g (e.symm (root C).val) ∈ A
  rw [hr]
  exact hg C

/-- An equivalent interface using a vertex-valued root choice and membership
proofs, rather than subtype-valued roots. -/
theorem common_list_forest_roots (roots : F.ConnectedComponent → V)
    (hroots : ∀ C, roots C ∈ C) {W : Type v} [Fintype W]
    (H : SimpleGraph W) (A : Finset W)
    (hdeg : ∀ s, F.edgeFinset.card ≤ H.degree s) (hA : Fintype.card V ≤ A.card) :
    ∃ f : F.Copy H, ∀ C, f (roots C) ∈ A :=
  common_list_forest F hF (fun C => ⟨roots C, hroots C⟩) H A hdeg hA

end StandardForestInterface

/-- **Theorem CL**, with a set-valued common list and the conventional minimum
degree and edge-set cardinality. There are no nonemptiness assumptions: empty
forests and marked isolated vertices are covered by the same statement. -/
theorem CL {V : Type u} [Fintype V] (F : SimpleGraph V) (hF : F.IsAcyclic)
    (roots : F.ConnectedComponent → V) (hroots : ∀ C, roots C ∈ C)
    {W : Type v} [Fintype W] (H : SimpleGraph W) (A : Set W)
    (hdeg : F.edgeSet.ncard ≤ H.minDegree) (hA : Fintype.card V ≤ A.ncard) :
    ∃ f : F.Copy H, ∀ C, f (roots C) ∈ A := by
  have he : F.edgeFinset.card = F.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card, Set.toFinite_toFinset]
    rfl
  have hAc : A.toFinset.card = A.ncard := by
    rw [Set.ncard_eq_toFinset_card, Set.toFinite_toFinset]
  obtain ⟨f, hf⟩ := common_list_forest_roots F hF roots hroots H A.toFinset
    (fun s => he ▸ hdeg.trans (H.minDegree_le_degree s)) (hAc ▸ hA)
  exact ⟨f, fun C => Set.mem_toFinset.mp (hf C)⟩

end CommonMarkedForest

-- Transitive kernel-dependency audit for the main interfaces.
#print axioms CommonMarkedForest.common_list_family
#print axioms CommonMarkedForest.common_list_forest
#print axioms CommonMarkedForest.CL
