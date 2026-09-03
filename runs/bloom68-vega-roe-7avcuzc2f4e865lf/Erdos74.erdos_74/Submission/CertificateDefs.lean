import FormalConjecturesUtil

/-!
# Finite edge certificates for Erdős problem 74

Endpoints, monochromatic edges, and their behavior under deletion, vertex maps,
and restriction to induced subgraphs. These lemmas use Boolean colorings directly,
without choosing a minimum bipartizing deletion.
-/

namespace Erdos74.Certificates

universe u
variable {V : Type u}

noncomputable def endVerts (E : Finset (Sym2 V)) : Finset V := by
  classical
  exact E.biUnion Sym2.toFinset

def mono (d : V → Bool) (e : Sym2 V) : Prop := (e.map d).IsDiag

@[simp] theorem mono_pair (d : V → Bool) (v w : V) :
    mono d s(v,w) ↔ d v = d w := by
  simp [mono]

def badGraph (G : SimpleGraph V) (c : V → Bool) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ c v = c w
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := fun v h => G.loopless v h.1

noncomputable def badEdges [Finite V] (G : SimpleGraph V) (c : V → Bool) :
    Finset (Sym2 V) := (badGraph G c).edgeSet.toFinite.toFinset

@[simp] theorem mem_badEdges [Finite V] (G : SimpleGraph V) (c : V → Bool)
    (v w : V) : s(v,w) ∈ badEdges G c ↔ G.Adj v w ∧ c v = c w := by
  simp [badEdges, SimpleGraph.mem_edgeSet, badGraph]

/- ## Endpoints of finite edge sets -/

@[simp] theorem mem_endVerts {E : Finset (Sym2 V)} {v : V} :
    v ∈ endVerts E ↔ ∃ e ∈ E, v ∈ e := by
  classical
  simp [endVerts]

theorem mem_endVerts_iff {E : Finset (Sym2 V)} {v : V} :
    v ∈ endVerts E ↔ ∃ w, s(v,w) ∈ E := by
  simp only [mem_endVerts, Sym2.mem_iff_exists]
  constructor
  · rintro ⟨e, he, w, rfl⟩
    exact ⟨w, he⟩
  · rintro ⟨w, hw⟩
    exact ⟨s(v,w), hw, w, rfl⟩

theorem left_mem_endVerts {E : Finset (Sym2 V)} {v w : V}
    (h : s(v,w) ∈ E) : v ∈ endVerts E :=
  mem_endVerts_iff.mpr ⟨w, h⟩

theorem right_mem_endVerts {E : Finset (Sym2 V)} {v w : V}
    (h : s(v,w) ∈ E) : w ∈ endVerts E :=
  mem_endVerts.mpr ⟨s(v,w), h, Sym2.mem_mk_right v w⟩

theorem endVerts_mono {E F : Finset (Sym2 V)} (h : E ⊆ F) :
    endVerts E ⊆ endVerts F := by
  rintro v hv
  obtain ⟨e, he, hv⟩ := mem_endVerts.mp hv
  exact mem_endVerts.mpr ⟨e, h he, hv⟩

@[simp] theorem endVerts_empty : endVerts (∅ : Finset (Sym2 V)) = ∅ := by
  classical
  simp [endVerts]

theorem endVerts_union (E F : Finset (Sym2 V)) [DecidableEq (Sym2 V)]
    [DecidableEq V] : endVerts (E ∪ F) = endVerts E ∪ endVerts F := by
  ext v
  simp only [mem_endVerts, Finset.mem_union]
  aesop

theorem card_endVerts_le (E : Finset (Sym2 V)) :
    (endVerts E).card ≤ 2 * E.card := by
  classical
  simpa only [endVerts, Nat.mul_comm] using
    (Finset.card_biUnion_le_card_mul E Sym2.toFinset 2 (by
      intro e _
      rw [Sym2.card_toFinset]
      split_ifs <;> omega))

/- ## Boolean colorings and monochromatic edges -/

instance instDecidableMono (d : V → Bool) (e : Sym2 V) : Decidable (mono d e) :=
  inferInstanceAs (Decidable (e.map d).IsDiag)

theorem mem_badEdges_iff [Finite V] (G : SimpleGraph V) (c : V → Bool)
    (e : Sym2 V) : e ∈ badEdges G c ↔ e ∈ G.edgeSet ∧ mono c e := by
  induction e using Sym2.ind with
  | h v w => simp

theorem badEdges_subset_edgeSet [Finite V] (G : SimpleGraph V) (c : V → Bool) :
    (badEdges G c : Set (Sym2 V)) ⊆ G.edgeSet := by
  intro e he
  exact ((mem_badEdges_iff G c e).mp he).1

theorem filter_mono_subset_badEdges [Finite V] (G : SimpleGraph V)
    (c : V → Bool) {Q : Finset (Sym2 V)} (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) :
    Q.filter (mono c) ⊆ badEdges G c := by
  intro e he
  obtain ⟨heQ, hec⟩ := Finset.mem_filter.mp he
  exact (mem_badEdges_iff G c e).mpr ⟨hQ heQ, hec⟩

theorem card_filter_mono_le_badEdges [Finite V] (G : SimpleGraph V)
    (c : V → Bool) {Q : Finset (Sym2 V)} (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) :
    (Q.filter (mono c)).card ≤ (badEdges G c).card :=
  Finset.card_le_card (filter_mono_subset_badEdges G c hQ)

/-- A proper Boolean coloring is a bipartite coloring, with no finiteness assumptions. -/
theorem isBipartite_of_bool_coloring {G : SimpleGraph V} (c : V → Bool)
    (hc : ∀ ⦃v w : V⦄, G.Adj v w → c v ≠ c w) : G.IsBipartite := by
  simpa using (SimpleGraph.Coloring.mk c (fun h => hc h)).colorable

theorem exists_bool_coloring_of_isBipartite {G : SimpleGraph V} (hG : G.IsBipartite) :
    ∃ c : V → Bool, ∀ ⦃v w : V⦄, G.Adj v w → c v ≠ c w := by
  let c : G.Coloring Bool := hG.toColoring (by simp)
  exact ⟨c, fun _ _ h => c.valid h⟩

theorem isBipartite_iff_exists_bool_coloring (G : SimpleGraph V) :
    G.IsBipartite ↔ ∃ c : V → Bool, ∀ ⦃v w : V⦄, G.Adj v w → c v ≠ c w :=
  ⟨exists_bool_coloring_of_isBipartite, fun ⟨c, hc⟩ => isBipartite_of_bool_coloring c hc⟩

theorem isBipartite_iff_nonempty_boolColoring (G : SimpleGraph V) :
    G.IsBipartite ↔ Nonempty (G.Coloring Bool) := by
  constructor
  · intro h
    exact ⟨h.toColoring (by simp)⟩
  · rintro ⟨c⟩
    exact isBipartite_of_bool_coloring c (fun _ _ h => c.valid h)

/-- A fixed coloring is proper after deletion exactly when all its bad edges are deleted. -/
theorem proper_deleteEdges_iff_badEdges_subset [Finite V] (G : SimpleGraph V)
    (c : V → Bool) (E : Set (Sym2 V)) :
    (∀ ⦃v w : V⦄, (G.deleteEdges E).Adj v w → c v ≠ c w) ↔
      (badEdges G c : Set (Sym2 V)) ⊆ E := by
  constructor
  · intro hc e he
    induction e using Sym2.ind with
    | h v w =>
      obtain ⟨hadj, heq⟩ := (mem_badEdges G c v w).mp he
      by_contra hE
      exact hc (SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hE⟩) heq
  · intro hE v w hvw heq
    obtain ⟨hadj, hnot⟩ := SimpleGraph.deleteEdges_adj.mp hvw
    exact hnot (hE ((mem_badEdges G c v w).mpr ⟨hadj, heq⟩))

theorem proper_delete_badEdges [Finite V] (G : SimpleGraph V) (c : V → Bool)
    {v w : V} (h : (G.deleteEdges (badEdges G c : Set (Sym2 V))).Adj v w) :
    c v ≠ c w :=
  (proper_deleteEdges_iff_badEdges_subset G c _).mpr Set.Subset.rfl h

theorem isBipartite_delete_badEdges [Finite V] (G : SimpleGraph V) (c : V → Bool) :
    (G.deleteEdges (badEdges G c : Set (Sym2 V))).IsBipartite :=
  isBipartite_of_bool_coloring c (fun _ _ h => proper_delete_badEdges G c h)

/-- One endpoint outside the endpoints of a set containing all bad edges suffices. -/
theorem proper_of_not_mem_endVerts [Finite V] {G : SimpleGraph V} {c : V → Bool}
    {F : Finset (Sym2 V)} (hF : badEdges G c ⊆ F) {v w : V}
    (hvw : G.Adj v w) (hv : v ∉ endVerts F) : c v ≠ c w := by
  intro heq
  exact hv (left_mem_endVerts (hF ((mem_badEdges G c v w).mpr ⟨hvw, heq⟩)))

theorem proper_off_badEdges [Finite V] {G : SimpleGraph V} {c : V → Bool}
    {v w : V} (hvw : G.Adj v w) (hv : v ∉ endVerts (badEdges G c)) : c v ≠ c w :=
  proper_of_not_mem_endVerts (fun _ h => h) hvw hv

theorem exists_badEdges_subset_of_isBipartite_deleteEdges [Finite V]
    {G : SimpleGraph V} {E : Set (Sym2 V)} (h : (G.deleteEdges E).IsBipartite) :
    ∃ c : V → Bool, (badEdges G c : Set (Sym2 V)) ⊆ E := by
  obtain ⟨c, hc⟩ := exists_bool_coloring_of_isBipartite h
  exact ⟨c, (proper_deleteEdges_iff_badEdges_subset G c E).mp hc⟩

theorem isBipartite_deleteEdges_iff_exists_badEdges_subset [Finite V]
    (G : SimpleGraph V) (E : Set (Sym2 V)) :
    (G.deleteEdges E).IsBipartite ↔
      ∃ c : V → Bool, (badEdges G c : Set (Sym2 V)) ⊆ E := by
  constructor
  · exact exists_badEdges_subset_of_isBipartite_deleteEdges
  · rintro ⟨c, hc⟩
    exact isBipartite_of_bool_coloring c
      ((proper_deleteEdges_iff_badEdges_subset G c E).mpr hc)

theorem exists_badEdges_subset_finset_of_isBipartite_deleteEdges [Finite V]
    {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (h : (G.deleteEdges (E : Set (Sym2 V))).IsBipartite) :
    ∃ c : V → Bool, badEdges G c ⊆ E :=
  exists_badEdges_subset_of_isBipartite_deleteEdges h

theorem exists_badEdges_card_le_of_isBipartite_deleteEdges [Finite V]
    {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (h : (G.deleteEdges (E : Set (Sym2 V))).IsBipartite) :
    ∃ c : V → Bool, badEdges G c ⊆ E ∧ (badEdges G c).card ≤ E.card := by
  obtain ⟨c, hc⟩ := exists_badEdges_subset_finset_of_isBipartite_deleteEdges h
  exact ⟨c, hc, Finset.card_le_card hc⟩

theorem exists_badEdges_card_le_ncard_of_isBipartite_deleteEdges [Finite V]
    {G : SimpleGraph V} {E : Set (Sym2 V)} (hE : E.Finite)
    (h : (G.deleteEdges E).IsBipartite) :
    ∃ c : V → Bool, (badEdges G c : Set (Sym2 V)) ⊆ E ∧
      (badEdges G c).card ≤ E.ncard := by
  obtain ⟨c, hc⟩ := exists_badEdges_subset_of_isBipartite_deleteEdges h
  exact ⟨c, hc, by simpa using Set.ncard_le_ncard hc hE⟩

/- ## Transport along vertex maps -/

universe v
variable {W : Type v}

@[simp] theorem mono_map (f : V → W) (d : W → Bool) (e : Sym2 V) :
    mono d (e.map f) ↔ mono (d ∘ f) e := by
  simp only [mono, Sym2.map_map]

theorem card_image_edges_le [DecidableEq W] (f : V → W) (Q : Finset (Sym2 V)) :
    (Q.image (Sym2.map f)).card ≤ Q.card :=
  Finset.card_image_le

theorem card_image_edges [DecidableEq W] (f : V → W) (hf : Function.Injective f)
    (Q : Finset (Sym2 V)) : (Q.image (Sym2.map f)).card = Q.card :=
  Finset.card_image_of_injective Q (Sym2.map.injective hf)

theorem mem_image_edges_iff [DecidableEq W] (f : V → W) (hf : Function.Injective f)
    (Q : Finset (Sym2 V)) (e : Sym2 V) :
    e.map f ∈ Q.image (Sym2.map f) ↔ e ∈ Q := by
  constructor
  · intro he
    obtain ⟨e', he', heq⟩ := Finset.mem_image.mp he
    exact (Sym2.map.injective hf heq) ▸ he'
  · exact Finset.mem_image_of_mem _

theorem image_edges_subset_edgeSet [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H)
    {Q : Finset (Sym2 V)} (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) :
    (Q.image (Sym2.map f) : Set (Sym2 W)) ⊆ H.edgeSet := by
  intro e he
  obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
  exact f.map_mem_edgeSet (hQ he')

theorem endVerts_image [DecidableEq W] (f : V → W) (Q : Finset (Sym2 V)) :
    endVerts (Q.image (Sym2.map f)) = (endVerts Q).image f := by
  ext w
  constructor
  · intro hw
    obtain ⟨e', he', hw⟩ := mem_endVerts.mp hw
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp he'
    obtain ⟨x, hx, hfx⟩ := Sym2.mem_map.mp hw
    exact Finset.mem_image.mpr ⟨x, mem_endVerts.mpr ⟨e, he, hx⟩, hfx⟩
  · intro hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨e, he, hxe⟩ := mem_endVerts.mp hx
    exact mem_endVerts.mpr ⟨e.map f, Finset.mem_image_of_mem _ he,
      Sym2.mem_map.mpr ⟨x, hxe, rfl⟩⟩

theorem card_endVerts_image_le [DecidableEq W] (f : V → W) (Q : Finset (Sym2 V)) :
    (endVerts (Q.image (Sym2.map f))).card ≤ (endVerts Q).card := by
  rw [endVerts_image]
  exact Finset.card_image_le

theorem card_endVerts_image [DecidableEq W] (f : V → W) (hf : Function.Injective f)
    (Q : Finset (Sym2 V)) :
    (endVerts (Q.image (Sym2.map f))).card = (endVerts Q).card := by
  rw [endVerts_image, Finset.card_image_of_injective _ hf]

theorem filter_mono_image [DecidableEq W] (f : V → W) (d : W → Bool)
    (Q : Finset (Sym2 V)) :
    (Q.image (Sym2.map f)).filter (mono d) =
      (Q.filter (mono (d ∘ f))).image (Sym2.map f) := by
  simp only [Finset.filter_image, mono_map]

theorem card_filter_mono_image [DecidableEq W] (f : V → W)
    (hf : Function.Injective f) (d : W → Bool) (Q : Finset (Sym2 V)) :
    ((Q.image (Sym2.map f)).filter (mono d)).card =
      (Q.filter (mono (d ∘ f))).card := by
  rw [filter_mono_image, card_image_edges f hf]

/-- Universal monochromatic-edge lower bounds transport by composing target colors with `f`. -/
theorem forall_card_filter_mono_image [DecidableEq W] (f : V → W)
    (hf : Function.Injective f) {Q : Finset (Sym2 V)} {k : ℕ}
    (hQ : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card) :
    ∀ d : W → Bool, k ≤ ((Q.image (Sym2.map f)).filter (mono d)).card := by
  intro d
  rw [card_filter_mono_image f hf]
  exact hQ (d ∘ f)

/-- The explicit image is an edge certificate with the same size bound. -/
theorem image_certificate [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) {Q : Finset (Sym2 V)} {k n : ℕ}
    (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) (hcard : Q.card ≤ n)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card) :
    (Q.image (Sym2.map f) : Set (Sym2 W)) ⊆ H.edgeSet ∧
      (Q.image (Sym2.map f)).card ≤ n ∧
      ∀ d : W → Bool, k ≤ ((Q.image (Sym2.map f)).filter (mono d)).card := by
  refine ⟨image_edges_subset_edgeSet f hQ, ?_, forall_card_filter_mono_image f hf hmono⟩
  simpa only [card_image_edges f hf] using hcard

theorem embedding_image_certificate [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ↪g H)
    {Q : Finset (Sym2 V)} {k n : ℕ}
    (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) (hcard : Q.card ≤ n)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card) :
    (Q.image (Sym2.map f) : Set (Sym2 W)) ⊆ H.edgeSet ∧
      (Q.image (Sym2.map f)).card ≤ n ∧
      ∀ d : W → Bool, k ≤ ((Q.image (Sym2.map f)).filter (mono d)).card :=
  image_certificate f.toHom f.injective hQ hcard hmono

/- ## Certificates supported on an induced subgraph -/

/-- Extend a Boolean coloring by `false` outside its domain. -/
theorem exists_bool_extension (S : Set V) (c : S → Bool) :
    ∃ d : V → Bool, (∀ v : S, d v = c v) ∧ ∀ v ∉ S, d v = false := by
  classical
  refine ⟨fun v => if h : v ∈ S then c ⟨v, h⟩ else false, ?_, ?_⟩
  · intro v
    simp only [dif_pos v.property]
  · intro v hv
    simp only [dif_neg hv]

/-- All monochromatic certificate edges supported on `S` are bad edges of the induced graph. -/
theorem card_filter_mono_le_badEdges_induce (G : SimpleGraph V) (Q : Finset (Sym2 V))
    (S : Set V) [Finite S] (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet)
    (hS : (endVerts Q : Set V) ⊆ S) (d : V → Bool) :
    (Q.filter (mono d)).card ≤ (badEdges (G.induce S) (fun v : S => d v)).card := by
  classical
  let B := badEdges (G.induce S) (fun v : S => d v)
  have hsub : Q.filter (mono d) ⊆ B.image (Sym2.map (Subtype.val : S → V)) := by
    intro e he
    induction e using Sym2.ind with
    | h v w =>
      obtain ⟨heQ, hec⟩ := Finset.mem_filter.mp he
      have hv : v ∈ S := hS (left_mem_endVerts heQ)
      have hw : w ∈ S := hS (right_mem_endVerts heQ)
      refine Finset.mem_image.mpr ⟨s((⟨v, hv⟩ : S), (⟨w, hw⟩ : S)), ?_, rfl⟩
      exact (mem_badEdges _ _ _ _).mpr
        ⟨hQ heQ, (mono_pair d v w).mp hec⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- A universal ambient certificate lower-bounds every coloring of an induced graph containing it. -/
theorem le_badEdges_induce_of_certificate {G : SimpleGraph V} {Q : Finset (Sym2 V)}
    {S : Set V} [Finite S] {k : ℕ} (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet)
    (hS : (endVerts Q : Set V) ⊆ S)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card) (c : S → Bool) :
    k ≤ (badEdges (G.induce S) c).card := by
  obtain ⟨d, hd, _⟩ := exists_bool_extension S c
  have heq : (fun v : S => d v) = c := funext hd
  have hle := card_filter_mono_le_badEdges_induce G Q S hQ hS d
  rw [heq] at hle
  exact (hmono d).trans hle

theorem le_badEdges_induce_finset_of_certificate
    {G : SimpleGraph V} {Q : Finset (Sym2 V)} {S : Finset V} {k : ℕ}
    (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) (hS : endVerts Q ⊆ S)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card)
    (c : S → Bool) : k ≤ (badEdges (G.induce (S : Set V)) c).card :=
  le_badEdges_induce_of_certificate (S := (S : Set V)) hQ hS hmono c

theorem le_card_bipartite_deletion_induce_of_certificate
    {G : SimpleGraph V} {Q : Finset (Sym2 V)} {S : Set V} [Finite S] {k : ℕ}
    (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) (hS : (endVerts Q : Set V) ⊆ S)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card)
    {E : Finset (Sym2 S)} (hbip : ((G.induce S).deleteEdges (E : Set (Sym2 S))).IsBipartite) :
    k ≤ E.card := by
  obtain ⟨c, _, hc⟩ := exists_badEdges_card_le_of_isBipartite_deleteEdges hbip
  exact (le_badEdges_induce_of_certificate hQ hS hmono c).trans hc

/-- Ambient edge deletion cannot bipartize the induced graph using fewer edges than its certificate.
The set `S` and the ambient vertex type need not be finite. -/
theorem le_card_ambient_deletion_of_certificate
    {G : SimpleGraph V} {Q : Finset (Sym2 V)} {S : Set V} {k : ℕ}
    (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) (hS : (endVerts Q : Set V) ⊆ S)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card)
    {E : Finset (Sym2 V)} (hbip : ((G.deleteEdges (E : Set (Sym2 V))).induce S).IsBipartite) :
    k ≤ E.card := by
  classical
  obtain ⟨c, hc⟩ := exists_bool_coloring_of_isBipartite hbip
  obtain ⟨d, hd, _⟩ := exists_bool_extension S c
  have hsub : Q.filter (mono d) ⊆ E := by
    intro e he
    induction e using Sym2.ind with
    | h v w =>
      obtain ⟨heQ, hec⟩ := Finset.mem_filter.mp he
      let v' : S := ⟨v, hS (left_mem_endVerts heQ)⟩
      let w' : S := ⟨w, hS (right_mem_endVerts heQ)⟩
      by_contra hnot
      have hadj : ((G.deleteEdges (E : Set (Sym2 V))).induce S).Adj v' w' :=
        SimpleGraph.deleteEdges_adj.mpr ⟨hQ heQ, hnot⟩
      apply hc hadj
      exact (hd v').symm.trans (((mono_pair d v w).mp hec).trans (hd w'))
  exact (hmono d).trans (Finset.card_le_card hsub)

theorem le_ncard_ambient_deletion_of_certificate
    {G : SimpleGraph V} {Q : Finset (Sym2 V)} {S : Set V} {k : ℕ}
    (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) (hS : (endVerts Q : Set V) ⊆ S)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card)
    {E : Set (Sym2 V)} (hE : E.Finite) (hbip : ((G.deleteEdges E).induce S).IsBipartite) :
    k ≤ E.ncard := by
  have hbip' : ((G.deleteEdges (hE.toFinset : Set (Sym2 V))).induce S).IsBipartite := by
    simpa only [hE.coe_toFinset] using hbip
  simpa only [Set.ncard_eq_toFinset_card E hE] using
    le_card_ambient_deletion_of_certificate hQ hS hmono hbip'

theorem not_isBipartite_induce_deleteEdges_of_card_lt
    {G : SimpleGraph V} {Q : Finset (Sym2 V)} {S : Set V} {k : ℕ}
    (hQ : (Q : Set (Sym2 V)) ⊆ G.edgeSet) (hS : (endVerts Q : Set V) ⊆ S)
    (hmono : ∀ d : V → Bool, k ≤ (Q.filter (mono d)).card)
    {E : Finset (Sym2 V)} (hE : E.card < k) :
    ¬((G.deleteEdges (E : Set (Sym2 V))).induce S).IsBipartite :=
  fun hbip => (Nat.not_le_of_lt hE) (le_card_ambient_deletion_of_certificate hQ hS hmono hbip)

end Erdos74.Certificates
