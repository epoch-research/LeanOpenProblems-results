import Submission.SubspaceRado

/-!
The dimension of the span of colored oriented incidence differences is the
number of colors times the spanning-forest rank. This is linear algebra only;
no cycle-absorption conclusion is asserted.
-/
open SimpleGraph Module
open scoped Classical
namespace Erdos184.ColoredIncidence

variable {K V I : Type*} [Field K] [Fintype V] [Fintype I]

noncomputable def root (G : SimpleGraph V) (c : G.ConnectedComponent) : V :=
  c.nonempty_supp.choose

lemma root_component (G : SimpleGraph V) (c : G.ConnectedComponent) :
    G.connectedComponentMk (root G c) = c :=
  (c.mem_supp_iff _).mp c.nonempty_supp.choose_spec

lemma root_injective (G : SimpleGraph V) : Function.Injective (root G) := by
  intro c d h
  have hh := congrArg G.connectedComponentMk h
  simpa only [root_component] using hh

abbrev Nonroot (G : SimpleGraph V) := {v : V // v ∉ Set.range (root G)}


lemma nonroot_ne_root (G : SimpleGraph V) (v : Nonroot G) (c : G.ConnectedComponent) :
    v.val ≠ root G c := by
  intro h
  exact v.property ⟨c, h.symm⟩

lemma card_nonroot (G : SimpleGraph V) :
    Fintype.card (Nonroot G) = Fintype.card V - Fintype.card G.ConnectedComponent := by
  have hc := Fintype.card_congr (Equiv.ofInjective (root G) (root_injective G))
  change Fintype.card {v : V // v ∉ Set.range (root G)} = _
  rw [Fintype.card_subtype_compl, ← hc]

noncomputable def boundary (i : I) (u v : V) : I → V → K :=
  fun j x => if j = i then (if x = u then 1 else 0) - (if x = v then 1 else 0) else 0

lemma boundary_self (i : I) (u : V) : boundary (K := K) i u u = 0 := by
  ext j x; simp [boundary]

lemma boundary_add (i : I) (u v w : V) :
    boundary (K := K) i u v + boundary i v w = boundary i u w := by
  ext j x
  by_cases h : j = i <;> simp [boundary, h]

noncomputable def generators (G : SimpleGraph V) : Set (I → V → K) :=
  {z | ∃ i u v, G.Adj u v ∧ z = boundary i u v}

noncomputable def edgeSpan (G : SimpleGraph V) : Submodule K (I → V → K) :=
  Submodule.span K (generators G)

lemma boundary_mem_edgeSpan (G : SimpleGraph V) (i : I) {u v : V} (h : G.Reachable u v) :
    boundary (K := K) i u v ∈ edgeSpan G := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rw [boundary_self]; exact (edgeSpan G).zero_mem
  | @cons u v w huv p ih =>
    rw [← boundary_add i u v w]
    exact (edgeSpan G).add_mem (Submodule.subset_span ⟨i, u, v, huv, rfl⟩) ih

noncomputable def rootVector (G : SimpleGraph V) (a : I × Nonroot G) : I → V → K :=
  boundary a.1 a.2.val (root G (G.connectedComponentMk a.2.val))

lemma rootVector_apply (G : SimpleGraph V) (a b : I × Nonroot G) :
    rootVector (K := K) G a b.1 b.2.val = if a = b then 1 else 0 := by
  have hn := nonroot_ne_root G b.2 (G.connectedComponentMk a.2.val)
  by_cases hc : b.1 = a.1
  · by_cases hv : b.2 = a.2
    · have he : a = b := Prod.ext hc.symm hv.symm
      subst b
      simp [rootVector, boundary, hn]
    · have hv' : b.2.val ≠ a.2.val := fun h => hv (Subtype.ext h)
      have he : a ≠ b := fun h => hv (congrArg Prod.snd h).symm
      simp [rootVector, boundary, hc, hv', hn, he]
  · have he : a ≠ b := fun h => hc (congrArg Prod.fst h).symm
    simp [rootVector, boundary, hc, he]

lemma rootVector_independent (G : SimpleGraph V) :
    LinearIndependent K (rootVector (K := K) (I := I) G) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro f hf a
  have hh := congrFun (congrFun hf a.1) a.2.val
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rootVector_apply,
    mul_ite] using hh

lemma rootVector_mem_edgeSpan (G : SimpleGraph V) (a : I × Nonroot G) :
    rootVector (K := K) G a ∈ edgeSpan G := by
  apply boundary_mem_edgeSpan
  apply ConnectedComponent.exact
  rw [root_component]

lemma boundary_to_root_mem (G : SimpleGraph V) (i : I) (v : V) :
    boundary (K := K) i v (root G (G.connectedComponentMk v)) ∈
      Submodule.span K (Set.range (rootVector (K := K) (I := I) G)) := by
  by_cases hv : v ∈ Set.range (root G)
  · obtain ⟨c, rfl⟩ := hv
    rw [root_component, boundary_self]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨⟨i, ⟨v, hv⟩⟩, rfl⟩

lemma edgeSpan_eq_root_span (G : SimpleGraph V) :
    edgeSpan (K := K) (I := I) G =
      Submodule.span K (Set.range (rootVector (K := K) (I := I) G)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, u, v, huv, rfl⟩
    have hu := boundary_to_root_mem (K := K) G i u
    have hv := boundary_to_root_mem (K := K) G i v
    have hc : G.connectedComponentMk u = G.connectedComponentMk v :=
      ConnectedComponent.sound huv.reachable
    rw [← hc] at hv
    have he : boundary (K := K) i u v =
        boundary i u (root G (G.connectedComponentMk u)) -
          boundary i v (root G (G.connectedComponentMk u)) := by
      ext j x
      by_cases h : j = i <;> simp [boundary, h]
    rw [he]
    exact Submodule.sub_mem _ hu hv
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact rootVector_mem_edgeSpan G a

/-- Colored incidence differences represent the direct sum of copies of
the graph's spanning-forest rank. -/
theorem finrank_edgeSpan (G : SimpleGraph V) :
    finrank K (edgeSpan (K := K) (I := I) G) =
      Fintype.card I * (Fintype.card V - Fintype.card G.ConnectedComponent) := by
  rw [edgeSpan_eq_root_span, finrank_span_eq_card (rootVector_independent G),
    Fintype.card_prod, card_nonroot]

lemma edgeSpan_mono {G H : SimpleGraph V} (h : G ≤ H) :
    edgeSpan (K := K) (I := I) G ≤ edgeSpan H := by
  apply Submodule.span_mono
  rintro _ ⟨i, u, v, huv, rfl⟩
  exact ⟨i, u, v, h huv, rfl⟩

lemma edgeSpan_finset_sup {J : Type*} (s : Finset J) (G : J → SimpleGraph V) :
    edgeSpan (K := K) (I := I) (s.sup G) = s.sup (fun j => edgeSpan (K := K) (I := I) (G j)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, u, v, huv, rfl⟩
    rw [Finset.sup_eq_iSup] at huv
    obtain ⟨j, hj⟩ := iSup_adj.mp huv
    obtain ⟨hjs, huv⟩ := iSup_adj.mp hj
    exact (Finset.le_sup (f := fun j => edgeSpan (K := K) (I := I) (G j)) hjs)
      (Submodule.subset_span ⟨i, u, v, huv, rfl⟩)
  · apply Finset.sup_le_iff.mpr
    intro j hj
    exact edgeSpan_mono (Finset.le_sup hj)

/-- A graph family satisfying the C-fold rank inequalities has one oriented,
colored representative edge per member, with independent incidence vectors. -/
theorem exists_independent_edges {J : Type*} [Fintype J]
    (G : J → SimpleGraph V)
    (h : ∀ s : Finset J, s.card ≤ Fintype.card I *
      (Fintype.card V - Fintype.card (s.sup G).ConnectedComponent)) :
    ∃ (c : J → I) (u v : J → V), (∀ j, (G j).Adj (u j) (v j)) ∧
      LinearIndependent ℚ (fun j => boundary (K := ℚ) (c j) (u j) (v j)) := by
  obtain ⟨w, hw, hi⟩ := SubspaceRado.exists_independent_representatives
    (fun j => generators (K := ℚ) (I := I) (G j)) (by
      intro s
      change s.card ≤ finrank ℚ ↥(s.sup (fun j => edgeSpan (K := ℚ) (I := I) (G j)))
      rw [← edgeSpan_finset_sup, finrank_edgeSpan]
      exact h s)
  choose c u v hadj he using hw
  refine ⟨c, u, v, hadj, ?_⟩
  have hw' : w = fun j => boundary (K := ℚ) (c j) (u j) (v j) := funext he
  rwa [← hw']

/-- Any submodule containing the incidence differences on adjacent pairs
also contains the difference on a reachable pair. -/
lemma boundary_mem_of_reachable (G : SimpleGraph V) (i : I)
    (W : Submodule K (I → V → K))
    (hW : ∀ u v, G.Adj u v → boundary i u v ∈ W)
    {u v : V} (huv : G.Reachable u v) : boundary i u v ∈ W := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => rw [boundary_self]; exact W.zero_mem
  | @cons u v w huv p ih =>
    rw [← boundary_add i u v w]
    exact W.add_mem (hW u v huv) ih

lemma boundary_reverse (i : I) (u v : V) :
    boundary (K := K) i v u = -boundary i u v := by
  ext j x
  by_cases h : j = i <;> simp [boundary, h]

end Erdos184.ColoredIncidence
