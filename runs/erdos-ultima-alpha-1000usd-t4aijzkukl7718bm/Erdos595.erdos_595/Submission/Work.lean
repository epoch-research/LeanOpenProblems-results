import FormalConjecturesUtil

/-!
# Scratch results for Erdős Problem 595

These are auxiliary results and obstructions to proposed constructions. They do
not prove or disprove the conjecture in `Submission/Spec.lean`.
-/

open SimpleGraph Set

namespace Erdos595Work

def IsCountableUnionOfTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

theorem countable_union_of_coloring {V : Type*} (G : SimpleGraph V)
    (f : G.Coloring (ℕ → Fin 2)) :
    IsCountableUnionOfTriangleFree G := by
  classical
  let H : ℕ → SimpleGraph V := fun n =>
    G ⊓ (⊤ : SimpleGraph (Fin 2)).comap (fun v => f v n)
  refine ⟨H, ?_, ?_⟩
  · intro n
    have hc : (H n).Colorable 2 :=
      ⟨SimpleGraph.Coloring.mk (fun v => f v n) (fun h => h.2)⟩
    exact hc.cliqueFree (by omega)
  · ext a b
    simp only [SimpleGraph.iSup_adj, H, SimpleGraph.inf_adj,
      SimpleGraph.comap_adj, SimpleGraph.top_adj]
    constructor
    · intro hab
      have hne : f a ≠ f b := f.valid hab
      have hcoord : ∃ n, f a n ≠ f b n := by
        by_contra h
        push_neg at h
        exact hne (funext h)
      obtain ⟨n, hn⟩ := hcoord
      exact ⟨n, hab, hn⟩
    · rintro ⟨n, h, _⟩
      exact h

theorem countable_union_of_binary_encoding {V : Type*} (G : SimpleGraph V)
    (f : V → ℕ → Fin 2) (hf : Function.Injective f) :
    IsCountableUnionOfTriangleFree G :=
  countable_union_of_coloring G
    (SimpleGraph.Coloring.mk f (fun h heq => h.ne (hf heq)))

#print axioms countable_union_of_coloring
#print axioms countable_union_of_binary_encoding


theorem no_adj_common_neighbors {V : Type*} {G : SimpleGraph V}
    (hG : G.CliqueFree 4) {a b c d : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (had : G.Adj a d) (hbd : G.Adj b d) : ¬ G.Adj c d := by
  classical
  intro hcd
  have ht : G.IsNClique 3 {a, b, c} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩
  apply hG _ (ht.insert (a := d) ?_)
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact had.symm
  · exact hbd.symm
  · exact hcd.symm

#print axioms no_adj_common_neighbors

/-- The edge-coloring formulation, with colors assigned to unordered pairs. -/
theorem countable_union_iff_edge_coloring {V : Type*} (G : SimpleGraph V) :
    IsCountableUnionOfTriangleFree G ↔
      ∃ c : Sym2 V → ℕ, ∀ a b d, G.Adj a b → G.Adj a d → G.Adj b d →
        ¬ (c s(a, b) = c s(a, d) ∧ c s(a, b) = c s(b, d)) := by
  classical
  constructor
  · rintro ⟨H, hH, hcov⟩
    have hex : ∀ e : Sym2 V, e ∈ G.edgeSet → ∃ n, e ∈ (H n).edgeSet := by
      intro e
      induction e using Sym2.inductionOn with
      | _ a b =>
        simp only [SimpleGraph.mem_edgeSet, hcov, SimpleGraph.iSup_adj]
        exact id
    let c : Sym2 V → ℕ := fun e =>
      if h : e ∈ G.edgeSet then (hex e h).choose else 0
    have hc : ∀ e (h : e ∈ G.edgeSet), e ∈ (H (c e)).edgeSet := by
      intro e h
      simp only [c, dif_pos h]
      exact (hex e h).choose_spec
    refine ⟨c, ?_⟩
    intro a b d hab had hbd heq
    have hab' : (H (c s(a, b))).Adj a b := hc s(a, b) hab
    have had' : (H (c s(a, b))).Adj a d := by
      rw [heq.1]
      exact hc s(a, d) had
    have hbd' : (H (c s(a, b))).Adj b d := by
      rw [heq.2]
      exact hc s(b, d) hbd
    exact hH _ _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab', had', hbd'⟩)
  · rintro ⟨c, hc⟩
    let H : ℕ → SimpleGraph V := fun n =>
      { Adj := fun a b => G.Adj a b ∧ c s(a, b) = n
        symm := by
          intro a b h
          exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩
        loopless := fun a h => G.loopless a h.1 }
    refine ⟨H, ?_, ?_⟩
    · intro n t ht
      obtain ⟨a, b, d, hab, had, hbd, _⟩ := SimpleGraph.is3Clique_iff.mp ht
      exact hc a b d hab.1 had.1 hbd.1
        ⟨hab.2.trans had.2.symm, hab.2.trans hbd.2.symm⟩
    · ext a b
      simp only [SimpleGraph.iSup_adj]
      change G.Adj a b ↔ ∃ n, G.Adj a b ∧ c s(a, b) = n
      simp

#print axioms countable_union_iff_edge_coloring


/-- A local criterion sufficient for a countable triangle-free edge cover. -/
theorem countable_union_of_earlier_neighbor_coloring {V : Type*} [LinearOrder V]
    (G : SimpleGraph V) (f : V → V → ℕ)
    (hf : ∀ a b d, b < a → d < a → G.Adj a b → G.Adj a d → G.Adj b d →
      f a b ≠ f a d) : IsCountableUnionOfTriangleFree G := by
  classical
  let c : Sym2 V → ℕ := Sym2.lift
    ⟨fun a b => f (max a b) (min a b), fun a b => by dsimp; rw [max_comm, min_comm]⟩
  apply (countable_union_iff_edge_coloring G).mpr
  refine ⟨c, ?_⟩
  intro a b d hab had hbd heq
  change f (max a b) (min a b) = f (max a d) (min a d) ∧
    f (max a b) (min a b) = f (max b d) (min b d) at heq
  rcases le_total a b with hab_le | hba_le
  · rcases le_total b d with hbd_le | hdb_le
    · have had_le := hab_le.trans hbd_le
      apply hf d a b (lt_of_le_of_ne had_le had.ne) (lt_of_le_of_ne hbd_le hbd.ne)
        had.symm hbd.symm hab
      simpa only [max_eq_right had_le, min_eq_left had_le,
        max_eq_right hbd_le, min_eq_left hbd_le] using heq.1.symm.trans heq.2
    · apply hf b a d (lt_of_le_of_ne hab_le hab.ne)
        (lt_of_le_of_ne hdb_le hbd.ne.symm) hab.symm hbd had
      simpa only [max_eq_right hab_le, min_eq_left hab_le,
        max_eq_left hdb_le, min_eq_right hdb_le] using heq.2
  · rcases le_total a d with had_le | hda_le
    · have hbd_le := hba_le.trans had_le
      apply hf d a b (lt_of_le_of_ne had_le had.ne) (lt_of_le_of_ne hbd_le hbd.ne)
        had.symm hbd.symm hab
      simpa only [max_eq_right had_le, min_eq_left had_le,
        max_eq_right hbd_le, min_eq_left hbd_le] using heq.1.symm.trans heq.2
    · apply hf a b d (lt_of_le_of_ne hba_le hab.ne.symm)
        (lt_of_le_of_ne hda_le had.ne.symm) hab had hbd
      simpa only [max_eq_left hba_le, min_eq_right hba_le,
        max_eq_left hda_le, min_eq_right hda_le] using heq.1

#print axioms countable_union_of_earlier_neighbor_coloring

/-- A graph with vertex chromatic cardinal at most the continuum admits the cover. -/
theorem countable_union_of_chromaticCardinal_le_continuum {V : Type}
    (G : SimpleGraph V) (hG : G.chromaticCardinal ≤ Cardinal.continuum) :
    IsCountableUnionOfTriangleFree G := by
  classical
  have hmem : G.chromaticCardinal ∈
      {κ : Cardinal | ∃ (C : Type) (_ : Cardinal.mk C = κ),
        Nonempty (G.Coloring C)} :=
    csInf_mem ⟨Cardinal.mk V, V, rfl, ⟨G.selfColoring⟩⟩
  obtain ⟨C, hC, ⟨f⟩⟩ := hmem
  have hcard : Cardinal.mk C ≤ Cardinal.mk (ℕ → Fin 2) := by
    simpa only [hC, Cardinal.mk_arrow, Cardinal.mk_fin, Cardinal.mk_nat,
      Cardinal.lift_uzero, Nat.cast_ofNat, Cardinal.two_power_aleph0] using hG
  have he : Nonempty (C ↪ (ℕ → Fin 2)) :=
    Cardinal.lift_mk_le'.mp (by simpa only [Cardinal.lift_uzero] using hcard)
  exact countable_union_of_coloring G (G.recolorOfEmbedding he.some f)

/-- Every possible witness has vertex chromatic cardinal strictly above the continuum. -/
theorem continuum_lt_chromaticCardinal_of_no_cover {V : Type} (G : SimpleGraph V)
    (hG : ¬IsCountableUnionOfTriangleFree G) :
    Cardinal.continuum < G.chromaticCardinal := by
  exact lt_of_not_ge fun h => hG (countable_union_of_chromaticCardinal_le_continuum G h)

#print axioms countable_union_of_chromaticCardinal_le_continuum
#print axioms continuum_lt_chromaticCardinal_of_no_cover

/-- It suffices to partition the vertices into continuum many triangle-free fibers. -/
theorem countable_union_of_triangle_free_fibers {V : Type*} (G : SimpleGraph V)
    (f : V → ℕ → Fin 2)
    (hf : ∀ a b d, G.Adj a b → G.Adj a d → G.Adj b d →
      ¬ (f a = f b ∧ f a = f d)) :
    IsCountableUnionOfTriangleFree G := by
  classical
  let T : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ f a = f b
      symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
      loopless := fun a h => G.loopless a h.1 }
  let H : ℕ → SimpleGraph V
    | 0 => T
    | n + 1 => G ⊓ (⊤ : SimpleGraph (Fin 2)).comap (fun v => f v n)
  refine ⟨H, ?_, ?_⟩
  · intro n
    cases n with
    | zero =>
      intro t ht
      obtain ⟨a, b, d, hab, had, hbd, _⟩ := SimpleGraph.is3Clique_iff.mp ht
      exact hf a b d hab.1 had.1 hbd.1 ⟨hab.2, had.2⟩
    | succ n =>
      have hc : (H (n + 1)).Colorable 2 :=
        ⟨SimpleGraph.Coloring.mk (fun v => f v n) (fun h => h.2)⟩
      exact hc.cliqueFree (by omega)
  · ext a b
    simp only [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      by_cases heq : f a = f b
      · exact ⟨0, hab, heq⟩
      · have hex : ∃ n, f a n ≠ f b n := by
          by_contra h
          push_neg at h
          exact heq (funext h)
        obtain ⟨n, hn⟩ := hex
        exact ⟨n + 1, hab, hn⟩
    · rintro ⟨n, hn⟩
      cases n <;> exact hn.1

/-- A witness is necessarily vertex-Ramsey for triangles with continuum many colors. -/
theorem monochromatic_vertex_triangle_of_no_cover {V : Type*} (G : SimpleGraph V)
    (hG : ¬IsCountableUnionOfTriangleFree G) (f : V → ℕ → Fin 2) :
    ∃ a b d, G.Adj a b ∧ G.Adj a d ∧ G.Adj b d ∧ f a = f b ∧ f a = f d := by
  by_contra h
  apply hG (countable_union_of_triangle_free_fibers G f ?_)
  intro a b d hab had hbd heq
  exact h ⟨a, b, d, hab, had, hbd, heq⟩

#print axioms countable_union_of_triangle_free_fibers
#print axioms monochromatic_vertex_triangle_of_no_cover

private def verticesAtLength {V : Type*} (G : SimpleGraph V) : ℕ → V → Set V
  | 0, u => {u}
  | n + 1, u => ⋃ v ∈ G.neighborSet u, verticesAtLength G n v

private theorem countable_verticesAtLength {V : Type*} (G : SimpleGraph V)
    (hG : ∀ v, (G.neighborSet v).Countable) (n : ℕ) (v : V) :
    (verticesAtLength G n v).Countable := by
  induction n generalizing v with
  | zero => exact Set.countable_singleton v
  | succ n ih => exact (hG v).biUnion fun w _ => ih w

private theorem mem_verticesAtLength {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) : v ∈ verticesAtLength G p.length u := by
  induction p with
  | nil => exact Set.mem_singleton _
  | @cons u w v h p ih =>
    exact Set.mem_iUnion_of_mem w (Set.mem_iUnion_of_mem h ih)

/-- The reachable set of any vertex of a locally countable graph is countable. -/
theorem countable_reachable_of_countable_neighbors {V : Type*} (G : SimpleGraph V)
    (hG : ∀ v, (G.neighborSet v).Countable) (v : V) :
    {w | G.Reachable v w}.Countable := by
  apply (Set.countable_iUnion fun n => countable_verticesAtLength G hG n v).mono
  rintro w ⟨p⟩
  exact Set.mem_iUnion_of_mem p.length (mem_verticesAtLength p)

/-- Every locally countable graph has a proper coloring by natural numbers. -/
theorem coloring_nat_of_countable_neighbors {V : Type*} (G : SimpleGraph V)
    (hG : ∀ v, (G.neighborSet v).Countable) : Nonempty (G.Coloring ℕ) := by
  classical
  refine ⟨G.homOfConnectedComponents fun c => ?_⟩
  have hc : c.supp.Countable := by
    obtain ⟨v, hv⟩ := c.nonempty_supp
    exact (countable_reachable_of_countable_neighbors G hG v).mono
      (fun w hw => c.reachable_of_mem_supp hv hw)
  letI : Countable c.supp := hc.to_subtype
  letI : Encodable c.supp := Encodable.ofCountable c.supp
  exact SimpleGraph.Coloring.mk Encodable.encode
    (fun h heq => h.ne (Encodable.encode_injective heq))

/-- Countable common neighborhoods suffice; no bound on the size of the whole graph is needed. -/
theorem countable_union_of_countable_common_neighbors {V : Type*} (G : SimpleGraph V)
    (hG : ∀ a b, G.Adj a b → {v | G.Adj a v ∧ G.Adj b v}.Countable) :
    IsCountableUnionOfTriangleFree G := by
  classical
  have hn : ∀ a, Nonempty ((G.induce (G.neighborSet a)).Coloring ℕ) := by
    intro a
    apply coloring_nat_of_countable_neighbors
    intro b
    have h := (hG a b b.property).preimage
      (f := fun v : G.neighborSet a => (v : V)) Subtype.val_injective
    apply h.mono
    intro v hv
    exact ⟨v.property, hv⟩
  let c : (a : V) → (G.induce (G.neighborSet a)).Coloring ℕ := fun a => (hn a).some
  let f : V → V → ℕ := fun a b => if h : G.Adj a b then c a ⟨b, h⟩ else 0
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  apply countable_union_of_earlier_neighbor_coloring G f
  intro a b d _ _ hab had hbd
  simpa only [f, dif_pos hab, dif_pos had] using (c a).valid (show
    (G.induce (G.neighborSet a)).Adj ⟨b, hab⟩ ⟨d, had⟩ from hbd)

#print axioms coloring_nat_of_countable_neighbors
#print axioms countable_union_of_countable_common_neighbors

private theorem exists_differing_bit {V : Type*} (f : V → ℕ → Fin 2)
    (hf : Function.Injective f) {a b : V} (h : a ≠ b) : ∃ n, f a n ≠ f b n := by
  by_contra hn
  push_neg at hn
  exact h (hf (funext hn))

noncomputable def firstDifference {V : Type*} (f : V → ℕ → Fin 2)
    (hf : Function.Injective f) (a b : V) : ℕ := by
  classical
  exact if h : a = b then 0 else Nat.find (exists_differing_bit f hf h)

private theorem firstDifference_spec {V : Type*} (f : V → ℕ → Fin 2)
    (hf : Function.Injective f) {a b : V} (hab : a ≠ b) :
    f a (firstDifference f hf a b) ≠ f b (firstDifference f hf a b) := by
  classical
  simpa only [firstDifference, dif_neg hab] using
    Nat.find_spec (exists_differing_bit f hf hab)

private theorem eq_before_firstDifference {V : Type*} (f : V → ℕ → Fin 2)
    (hf : Function.Injective f) {a b : V} (hab : a ≠ b) {n : ℕ}
    (hn : n < firstDifference f hf a b) : f a n = f b n := by
  classical
  simp only [firstDifference, dif_neg hab] at hn
  exact not_not.mp (Nat.find_min (exists_differing_bit f hf hab) hn)

private theorem firstDifference_eq_of_bits {V : Type*} (f : V → ℕ → Fin 2)
    (hf : Function.Injective f) {a b : V} (hab : a ≠ b) {n : ℕ}
    (hn : f a n ≠ f b n) (hbefore : ∀ k < n, f a k = f b k) :
    firstDifference f hf a b = n := by
  classical
  simp only [firstDifference, dif_neg hab]
  exact (Nat.find_eq_iff (exists_differing_bit f hf hab)).mpr
    ⟨hn, fun k hk h => h (hbefore k hk)⟩

private theorem firstDifference_symm {V : Type*} (f : V → ℕ → Fin 2)
    (hf : Function.Injective f) (a b : V) :
    firstDifference f hf a b = firstDifference f hf b a := by
  classical
  by_cases hab : a = b
  · subst b; rfl
  · apply firstDifference_eq_of_bits f hf hab
    · exact (firstDifference_spec f hf (Ne.symm hab)).symm
    · intro k hk
      exact (eq_before_firstDifference f hf (Ne.symm hab) hk).symm

private theorem firstDifference_of_lt {V : Type*} (f : V → ℕ → Fin 2)
    (hf : Function.Injective f) {a b t : V} (hat : a ≠ t) (hbt : b ≠ t)
    (hab : a ≠ b) (h : firstDifference f hf a t < firstDifference f hf b t) :
    firstDifference f hf a b = firstDifference f hf a t := by
  apply firstDifference_eq_of_bits f hf hab
  · rw [eq_before_firstDifference f hf hbt h]
    exact firstDifference_spec f hf hat
  · intro k hk
    exact (eq_before_firstDifference f hf hat hk).trans
      (eq_before_firstDifference f hf hbt (hk.trans h)).symm

private theorem firstDifference_ne_of_eq {V : Type*} (f : V → ℕ → Fin 2)
    (hf : Function.Injective f) {a b t : V} (hat : a ≠ t) (hbt : b ≠ t)
    (hab : a ≠ b) (h : firstDifference f hf a t = firstDifference f hf b t) :
    firstDifference f hf a b ≠ firstDifference f hf a t := by
  intro heq
  have ha := firstDifference_spec f hf hat
  have hb := firstDifference_spec f hf hbt
  have hab' := firstDifference_spec f hf hab
  rw [← h] at hb
  rw [heq] at hab'
  have he : f a (firstDifference f hf a t) = f b (firstDifference f hf a t) := by
    have ha' := (f a (firstDifference f hf a t)).isLt
    have hb' := (f b (firstDifference f hf a t)).isLt
    have ht' := (f t (firstDifference f hf a t)).isLt
    apply Fin.ext
    have ha'' : (f a (firstDifference f hf a t)).val ≠
        (f t (firstDifference f hf a t)).val := fun h => ha (Fin.ext h)
    have hb'' : (f b (firstDifference f hf a t)).val ≠
        (f t (firstDifference f hf a t)).val := fun h => hb (Fin.ext h)
    omega
  exact hab' he

/-- First-difference edge labels on an injectively binary-encoded triangle-free graph
admit an adapted vertex labeling. This is a special case, not the unrestricted extension lemma. -/
theorem adapted_firstDifference {V : Type*} (G : SimpleGraph V)
    (hG : G.CliqueFree 3) (f : V → ℕ → Fin 2) (hf : Function.Injective f) (t : V) :
    ∃ g : V → ℕ, ∀ a b, G.Adj a b →
      ¬ (g a = firstDifference f hf a b ∧ g b = firstDifference f hf a b) := by
  classical
  let g : V → ℕ := fun v => if v = t then 0 else
    if G.Adj t v then firstDifference f hf v t + 1 else firstDifference f hf v t
  refine ⟨g, ?_⟩
  intro a b hab heq
  by_cases hat : a = t
  · subst a
    have hbt : b ≠ t := hab.ne.symm
    simp only [g, if_pos rfl, if_neg hbt, if_pos hab] at heq
    omega
  by_cases hbt : b = t
  · subst b
    simp only [g, if_neg hat, if_pos hab.symm, if_pos rfl] at heq
    omega
  by_cases hta : G.Adj t a
  · by_cases htb : G.Adj t b
    · exact hG _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hta, htb, hab⟩)
    · simp only [g, if_neg hat, if_neg hbt, if_pos hta, if_neg htb] at heq
      have hlt : firstDifference f hf a t < firstDifference f hf b t := by omega
      have he := firstDifference_of_lt f hf hat hbt hab.ne hlt
      omega
  · by_cases htb : G.Adj t b
    · simp only [g, if_neg hat, if_neg hbt, if_neg hta, if_pos htb] at heq
      have hlt : firstDifference f hf b t < firstDifference f hf a t := by omega
      have he := firstDifference_of_lt f hf hbt hat hab.ne.symm hlt
      rw [firstDifference_symm f hf b a] at he
      omega
    · simp only [g, if_neg hat, if_neg hbt, if_neg hta, if_neg htb] at heq
      exact firstDifference_ne_of_eq f hf hat hbt hab.ne (heq.1.trans heq.2.symm)
        heq.1.symm

#print axioms adapted_firstDifference


private theorem mk_verticesAtLength_le {V : Type} (G : SimpleGraph V)
    (hG : ∀ v, Cardinal.mk (G.neighborSet v) ≤ Cardinal.continuum) (n : ℕ) (v : V) :
    Cardinal.mk (verticesAtLength G n v) ≤ Cardinal.continuum := by
  induction n generalizing v with
  | zero =>
    simpa only [verticesAtLength, Cardinal.mk_singleton] using
      (Cardinal.one_le_aleph0.trans Cardinal.aleph0_le_continuum)
  | succ n ih =>
    exact (Cardinal.mk_biUnion_le (verticesAtLength G n) (G.neighborSet v)).trans
      ((mul_le_mul' (hG v) (ciSup_le' fun w : G.neighborSet v => ih w)).trans_eq
        (Cardinal.mul_eq_self Cardinal.aleph0_le_continuum))

/-- A continuum bound on degrees also bounds each connected component. -/
theorem mk_reachable_le_continuum {V : Type} (G : SimpleGraph V)
    (hG : ∀ v, Cardinal.mk (G.neighborSet v) ≤ Cardinal.continuum) (v : V) :
    Cardinal.mk {w | G.Reachable v w} ≤ Cardinal.continuum := by
  apply (Cardinal.mk_le_mk_of_subset (show {w | G.Reachable v w} ⊆
    ⋃ n, verticesAtLength G n v from ?_)).trans
  · refine (Cardinal.mk_iUnion_le (fun n => verticesAtLength G n v)).trans ?_
    apply (mul_le_mul' ?_ (ciSup_le' fun n => mk_verticesAtLength_le G hG n v)).trans_eq
      (Cardinal.mul_eq_self Cardinal.aleph0_le_continuum)
    simpa only [Cardinal.mk_nat] using Cardinal.aleph0_le_continuum
  · rintro w ⟨p⟩
    exact Set.mem_iUnion_of_mem p.length (mem_verticesAtLength p)

/-- Ordered edges are joined by reversal and by lying in the same triangle. -/
private def triangleDartGraph {V : Type} (G : SimpleGraph V) : SimpleGraph (V × V) where
  Adj p q := (p.1 ≠ p.2 ∧ q = (p.2, p.1)) ∨
    (p.1 = q.1 ∧ G.Adj p.1 p.2 ∧ G.Adj q.1 q.2 ∧ G.Adj p.2 q.2)
  symm := by
    rintro ⟨a, b⟩ ⟨c, d⟩ (⟨hne, heq⟩ | ⟨h, hab, hcd, hbd⟩)
    · cases heq
      exact Or.inl ⟨hne.symm, rfl⟩
    · exact Or.inr ⟨h.symm, hcd, hab, hbd.symm⟩
  loopless := by
    rintro ⟨a, b⟩ (⟨hne, heq⟩ | ⟨_, _, _, hbb⟩)
    · exact hne (Prod.mk.inj heq).1
    · exact G.loopless b hbb

private theorem mk_triangleDartGraph_neighbors_le {V : Type} (G : SimpleGraph V)
    (hG : ∀ a b, G.Adj a b →
      Cardinal.mk {v | G.Adj a v ∧ G.Adj b v} ≤ Cardinal.continuum) (p : V × V) :
    Cardinal.mk ((triangleDartGraph G).neighborSet p) ≤ Cardinal.continuum := by
  classical
  rcases p with ⟨a, b⟩
  by_cases hab : G.Adj a b
  · apply (Cardinal.mk_le_mk_of_subset (show (triangleDartGraph G).neighborSet (a, b) ⊆
        {(b, a)} ∪ (fun c => (a, c)) '' {v | G.Adj a v ∧ G.Adj b v} from ?_)).trans
    · exact (Cardinal.mk_union_le _ _).trans
        (Cardinal.add_le_of_le Cardinal.aleph0_le_continuum
          (by simpa using Cardinal.one_le_aleph0.trans Cardinal.aleph0_le_continuum)
          (Cardinal.mk_image_le.trans (hG a b hab)))
    · rintro ⟨c, d⟩ (⟨_, heq⟩ | ⟨h, _, had, hbd⟩)
      · exact Or.inl heq
      · cases h
        exact Or.inr ⟨d, ⟨had, hbd⟩, rfl⟩
  · apply (Cardinal.mk_le_mk_of_subset (show (triangleDartGraph G).neighborSet (a, b) ⊆
        {(b, a)} from ?_)).trans
    · simpa using Cardinal.one_le_aleph0.trans Cardinal.aleph0_le_continuum
    · rintro ⟨c, d⟩ (⟨_, heq⟩ | ⟨_, hab', _⟩)
      · exact heq
      · exact (hab hab').elim

#print axioms mk_reachable_le_continuum
#print axioms mk_triangleDartGraph_neighbors_le


/-- Continuum-sized common neighborhoods suffice for a countable triangle-free cover.
The proof colors each triangle-connected component independently. -/
theorem countable_union_of_common_neighbors_le_continuum {V : Type} (G : SimpleGraph V)
    (hG : ∀ a b, G.Adj a b →
      Cardinal.mk {v | G.Adj a v ∧ G.Adj b v} ≤ Cardinal.continuum) :
    IsCountableUnionOfTriangleFree G := by
  classical
  let T := triangleDartGraph G
  let S : T.ConnectedComponent → Set V := fun C => Prod.fst '' C.supp
  have hS : ∀ C, Cardinal.mk (S C) ≤ Cardinal.continuum := by
    intro C
    obtain ⟨p, hp⟩ := C.nonempty_supp
    exact Cardinal.mk_image_le.trans
      ((Cardinal.mk_le_mk_of_subset (show C.supp ⊆ {q | T.Reachable p q} from
        fun q hq => C.reachable_of_mem_supp hp hq)).trans
        (mk_reachable_le_continuum T (mk_triangleDartGraph_neighbors_le G hG) p))
  have he : ∀ C, Nonempty (S C ↪ (ℕ → Fin 2)) := by
    intro C
    apply Cardinal.lift_mk_le'.mp
    simpa only [Cardinal.lift_uzero, Cardinal.mk_arrow, Cardinal.mk_fin,
      Cardinal.mk_nat, Nat.cast_ofNat, Cardinal.two_power_aleph0] using hS C
  let f : ∀ C, S C ↪ (ℕ → Fin 2) := fun C => (he C).some
  let code : T.ConnectedComponent → V → ℕ → Fin 2 := fun C v =>
    if hv : v ∈ S C then f C ⟨v, hv⟩ else fun _ => 0
  have code_ne : ∀ C a b, a ∈ S C → b ∈ S C → a ≠ b → code C a ≠ code C b := by
    intro C a b ha hb hab hh
    simp only [code, dif_pos ha, dif_pos hb] at hh
    exact hab (congrArg Subtype.val ((f C).injective hh))
  have swap_cc : ∀ a b, T.connectedComponentMk (a, b) = T.connectedComponentMk (b, a) := by
    intro a b
    by_cases hab : a = b
    · subst b; rfl
    · exact SimpleGraph.ConnectedComponent.eq.mpr
        ((show T.Adj (a, b) (b, a) from Or.inl ⟨hab, rfl⟩).reachable)
  have memS : ∀ a b, a ∈ S (T.connectedComponentMk (a, b)) ∧
      b ∈ S (T.connectedComponentMk (a, b)) := by
    intro a b
    constructor
    · exact ⟨(a, b), (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl, rfl⟩
    · exact ⟨(b, a), (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
        (swap_cc a b).symm, rfl⟩
  let c₀ : V → V → ℕ := fun a b => firstDifference id Function.injective_id
    (code (T.connectedComponentMk (a, b)) a) (code (T.connectedComponentMk (a, b)) b)
  have hc₀ : ∀ a b, c₀ a b = c₀ b a := by
    intro a b
    dsimp only [c₀]
    rw [swap_cc a b]
    exact firstDifference_symm id Function.injective_id _ _
  let c : Sym2 V → ℕ := Sym2.lift ⟨c₀, hc₀⟩
  apply (countable_union_iff_edge_coloring G).mpr
  refine ⟨c, ?_⟩
  intro a b d hab had hbd hmono
  have hac : T.connectedComponentMk (a, b) = T.connectedComponentMk (a, d) :=
    SimpleGraph.ConnectedComponent.eq.mpr
      ((show T.Adj (a, b) (a, d) from Or.inr ⟨rfl, hab, had, hbd⟩).reachable)
  have hbc : T.connectedComponentMk (a, b) = T.connectedComponentMk (b, d) :=
    (swap_cc a b).trans (SimpleGraph.ConnectedComponent.eq.mpr
      ((show T.Adj (b, a) (b, d) from Or.inr ⟨rfl, hab.symm, hbd, had⟩).reachable))
  let C := T.connectedComponentMk (a, b)
  have ha : a ∈ S C := (memS a b).1
  have hb : b ∈ S C := (memS a b).2
  have hd : d ∈ S C := by
    dsimp only [C]
    rw [hac]
    exact (memS a d).2
  change firstDifference id Function.injective_id (code C a) (code C b) =
      firstDifference id Function.injective_id
        (code (T.connectedComponentMk (a, d)) a) (code (T.connectedComponentMk (a, d)) d) ∧
    firstDifference id Function.injective_id (code C a) (code C b) =
      firstDifference id Function.injective_id
        (code (T.connectedComponentMk (b, d)) b) (code (T.connectedComponentMk (b, d)) d)
    at hmono
  rw [← hac, ← hbc] at hmono
  exact firstDifference_ne_of_eq id Function.injective_id
    (code_ne C a d ha hd had.ne) (code_ne C b d hb hd hbd.ne)
    (code_ne C a b ha hb hab.ne) (hmono.1.symm.trans hmono.2) hmono.1

/-- Any counterexample to countable covering has an edge with more than continuum many
common neighbors. In a `K₄`-free graph those common neighbors are independent. -/
theorem exists_large_common_neighbors_of_no_cover {V : Type} (G : SimpleGraph V)
    (hG : ¬IsCountableUnionOfTriangleFree G) :
    ∃ a b, G.Adj a b ∧ Cardinal.continuum < Cardinal.mk {v | G.Adj a v ∧ G.Adj b v} := by
  by_contra hn
  push_neg at hn
  exact hG (countable_union_of_common_neighbors_le_continuum G hn)

#print axioms countable_union_of_common_neighbors_le_continuum
#print axioms exists_large_common_neighbors_of_no_cover


/-- Keep exactly the edges internal to one fiber, retaining the ambient vertex type. -/
def vertexPiece {V I : Type*} (G : SimpleGraph V) (f : V → I) (i : I) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ f a = i ∧ f b = i
  symm := fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := fun a h => G.loopless a h.1

/-- Countable triangle-free covering is closed under vertex partitions with at most
continuum many pieces, provided each piece has the covering property. -/
theorem countable_union_of_vertex_pieces {V : Type*} (G : SimpleGraph V)
    (f : V → ℕ → Fin 2)
    (hf : ∀ i, IsCountableUnionOfTriangleFree (vertexPiece G f i)) :
    IsCountableUnionOfTriangleFree G := by
  classical
  choose H hH hcov using hf
  have hle : ∀ i n, H i n ≤ vertexPiece G f i := by
    intro i n
    rw [hcov i]
    exact le_iSup (H i) n
  let L : ℕ → SimpleGraph V := fun n => ⨆ i, H i n
  have hL : ∀ n, (L n).CliqueFree 3 := by
    intro n t ht
    obtain ⟨a, b, d, hab, had, hbd, _⟩ := SimpleGraph.is3Clique_iff.mp ht
    obtain ⟨i, hi⟩ := SimpleGraph.iSup_adj.mp hab
    obtain ⟨j, hj⟩ := SimpleGraph.iSup_adj.mp had
    obtain ⟨k, hk⟩ := SimpleGraph.iSup_adj.mp hbd
    have hij : j = i := ((hle j n hj).2.1).symm.trans (hle i n hi).2.1
    have hik : k = i := ((hle k n hk).2.1).symm.trans (hle i n hi).2.2
    subst j; subst k
    exact hH i n _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hi, hj, hk⟩)
  let B : ℕ → SimpleGraph V := fun n =>
    G ⊓ (⊤ : SimpleGraph (Fin 2)).comap (fun v => f v n)
  have hB : ∀ n, (B n).CliqueFree 3 := by
    intro n
    have hc : (B n).Colorable 2 :=
      ⟨SimpleGraph.Coloring.mk (fun v => f v n) (fun h => h.2)⟩
    exact hc.cliqueFree (by omega)
  let K : ℕ → SimpleGraph V := fun n =>
    if (Nat.unpair n).1 = 0 then L (Nat.unpair n).2 else B (Nat.unpair n).2
  refine ⟨K, ?_, ?_⟩
  · intro n
    dsimp only [K]
    split_ifs
    · exact hL _
    · exact hB _
  · ext a b
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      by_cases heq : f a = f b
      · have hp : (vertexPiece G f (f a)).Adj a b := ⟨hab, rfl, heq.symm⟩
        rw [hcov (f a), SimpleGraph.iSup_adj] at hp
        obtain ⟨n, hn⟩ := hp
        refine ⟨Nat.pair 0 n, ?_⟩
        simp only [K, Nat.unpair_pair]
        exact SimpleGraph.iSup_adj.mpr ⟨f a, hn⟩
      · have hex : ∃ n, f a n ≠ f b n := by
          by_contra h
          push_neg at h
          exact heq (funext h)
        obtain ⟨n, hn⟩ := hex
        refine ⟨Nat.pair 1 n, ?_⟩
        simpa only [K, Nat.unpair_pair, if_neg (show (1 : ℕ) ≠ 0 by decide), B,
          SimpleGraph.inf_adj, SimpleGraph.comap_adj, SimpleGraph.top_adj] using ⟨hab, hn⟩
    · rintro ⟨n, hn⟩
      dsimp only [K] at hn
      split_ifs at hn
      · obtain ⟨i, hi⟩ := SimpleGraph.iSup_adj.mp hn
        exact (hle i _ hi).1
      · exact hn.1

/-- A witness cannot be partitioned into continuum many coverable induced pieces. -/
theorem exists_vertex_piece_without_cover {V : Type*} (G : SimpleGraph V)
    (hG : ¬IsCountableUnionOfTriangleFree G) (f : V → ℕ → Fin 2) :
    ∃ i, ¬IsCountableUnionOfTriangleFree (vertexPiece G f i) := by
  by_contra! hn
  exact hG (countable_union_of_vertex_pieces G f hn)

#print axioms countable_union_of_vertex_pieces
#print axioms exists_vertex_piece_without_cover


/-- The directed Fubini extension of a graph's adjacency relation. -/
def fubiniAdj {V : Type*} (G : SimpleGraph V) (p q : Ultrafilter V) : Prop :=
  {v | G.neighborSet v ∈ q} ∈ p

/-- Six forward Fubini adjacencies already yield a genuine `K₄` in the original graph. -/
theorem no_four_fubini {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (p q r s : Ultrafilter V)
    (hpq : fubiniAdj G p q) (hpr : fubiniAdj G p r) (hps : fubiniAdj G p s)
    (hqr : fubiniAdj G q r) (hqs : fubiniAdj G q s) (hrs : fubiniAdj G r s) : False := by
  obtain ⟨a, haq, har, has⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem hpq (Filter.inter_mem hpr hps))
  obtain ⟨b, hab, hbr, hbs⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem haq (Filter.inter_mem hqr hqs))
  obtain ⟨c, hac, hbc, hcs⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem har (Filter.inter_mem hbr hrs))
  obtain ⟨d, had, hbd, hcd⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem has (Filter.inter_mem hbs hcs))
  exact no_adj_common_neighbors hG hab hac hbc had hbd hcd

/-- Symmetrizing the Fubini relation produces a simple graph when the original is `K₄`-free. -/
def ultrafilterGraph {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    SimpleGraph (Ultrafilter V) where
  Adj p q := fubiniAdj G p q ∧ fubiniAdj G q p
  symm := fun _ _ h => h.symm
  loopless := fun p h => no_four_fubini G hG p p p p h.1 h.1 h.1 h.1 h.1 h.1

theorem ultrafilterGraph_cliqueFree {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    (ultrafilterGraph G hG).CliqueFree 4 := by
  classical
  by_contra hn
  let f : (⊤ : SimpleGraph (Fin 4)) ↪g ultrafilterGraph G hG :=
    SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have hadj : ∀ i j : Fin 4, i ≠ j → (ultrafilterGraph G hG).Adj (f i) (f j) := by
    intro i j hij
    exact f.map_rel_iff.mpr (by simpa only [SimpleGraph.top_adj] using hij)
  exact no_four_fubini G hG (f 0) (f 1) (f 2) (f 3)
    (hadj 0 1 (by decide)).1 (hadj 0 2 (by decide)).1 (hadj 0 3 (by decide)).1
    (hadj 1 2 (by decide)).1 (hadj 1 3 (by decide)).1 (hadj 2 3 (by decide)).1

/-- The neighborhood trace on the original vertex set is a proper vertex coloring
of the symmetric ultrafilter extension. -/
theorem ultrafilterGraph_trace_coloring {V : Type*} (G : SimpleGraph V)
    (hG : G.CliqueFree 4) : Nonempty ((ultrafilterGraph G hG).Coloring (Set V)) := by
  refine ⟨SimpleGraph.Coloring.mk (fun p => {v | G.neighborSet v ∈ p}) ?_⟩
  intro p q hpq heq
  dsimp only at heq
  have hpp : fubiniAdj G p p := by
    change {v | G.neighborSet v ∈ p} ∈ p
    rw [heq]
    exact hpq.1
  exact no_four_fubini G hG p p p p hpp hpp hpp hpp hpp hpp

#print axioms no_four_fubini
#print axioms ultrafilterGraph_cliqueFree
#print axioms ultrafilterGraph_trace_coloring


/-- One symmetric ultrafilter extension of a countable `K₄`-free graph is still
countably coverable by triangle-free graphs, despite its potentially huge vertex set. -/
theorem countable_union_ultrafilterGraph_of_countable {V : Type} [Countable V]
    (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    IsCountableUnionOfTriangleFree (ultrafilterGraph G hG) := by
  classical
  have hcard : Cardinal.mk (Set V) ≤ Cardinal.mk (ℕ → Fin 2) := by
    simp only [Cardinal.mk_set, Cardinal.mk_arrow, Cardinal.mk_fin, Cardinal.mk_nat,
      Cardinal.lift_uzero, Nat.cast_ofNat]
    exact Cardinal.power_le_power_left (by simp) Cardinal.mk_le_aleph0
  have he : Nonempty (Set V ↪ (ℕ → Fin 2)) :=
    Cardinal.lift_mk_le'.mp (by simpa only [Cardinal.lift_uzero] using hcard)
  exact countable_union_of_coloring _
    ((ultrafilterGraph G hG).recolorOfEmbedding he.some
      (ultrafilterGraph_trace_coloring G hG).some)

#print axioms countable_union_ultrafilterGraph_of_countable


/-- Fubini adjacencies between ultrafilters supported on a triangle-free induced
subgraph cannot form a forward triangle. -/
private theorem no_three_fubini_on {V : Type*} (G : SimpleGraph V) (S : Set V)
    (hS : (G.induce S).CliqueFree 3) (p q r : Ultrafilter V)
    (hp : S ∈ p) (hq : S ∈ q) (hr : S ∈ r)
    (hpq : fubiniAdj G p q) (hpr : fubiniAdj G p r) (hqr : fubiniAdj G q r) :
    False := by
  classical
  obtain ⟨a, haS, haq, har⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem hp (Filter.inter_mem hpq hpr))
  obtain ⟨b, hbS, hab, hbr⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem hq (Filter.inter_mem haq hqr))
  obtain ⟨c, hcS, hac, hbc⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem hr (Filter.inter_mem har hbr))
  exact hS _ (SimpleGraph.is3Clique_triple_iff.mpr
    (show (G.induce S).Adj ⟨a, haS⟩ ⟨b, hbS⟩ ∧
      (G.induce S).Adj ⟨a, haS⟩ ⟨c, hcS⟩ ∧
      (G.induce S).Adj ⟨b, hbS⟩ ⟨c, hcS⟩ from ⟨hab, hac, hbc⟩))

/-- Taking the ultrafilter extension preserves triangle-freeness on a supported set. -/
theorem ultrafilterGraph_support_cliqueFree {V : Type*} (G : SimpleGraph V)
    (hG : G.CliqueFree 4) (S : Set V) (hS : (G.induce S).CliqueFree 3) :
    ((ultrafilterGraph G hG).induce {p | S ∈ p}).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨p, q, r, hpq, hpr, hqr, _⟩ := SimpleGraph.is3Clique_iff.mp ht
  exact no_three_fubini_on G S hS p q r p.property q.property r.property
    hpq.1 hpr.1 hqr.1

/-- The original vertices adjacent to an ultrafilter induce a triangle-free graph. -/
theorem ultrafilter_trace_cliqueFree {V : Type*} (G : SimpleGraph V)
    (hG : G.CliqueFree 4) (p : Ultrafilter V) :
    (G.induce {v | G.neighborSet v ∈ p}).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp ht
  obtain ⟨d, had, hbd, hcd⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem a.property (Filter.inter_mem b.property c.property))
  exact no_adj_common_neighbors hG hab hac hbc had hbd hcd

/-- A nonisolated vertex in the second extension is supported on the double
ultrafilter extension of a triangle-free subset of the original graph. -/
theorem second_ultrafilter_support {V : Type*} (G : SimpleGraph V)
    (hG : G.CliqueFree 4) (P Q : Ultrafilter (Ultrafilter V))
    (hPQ : (ultrafilterGraph (ultrafilterGraph G hG)
      (ultrafilterGraph_cliqueFree G hG)).Adj P Q) :
    ∃ S : Set V, (G.induce S).CliqueFree 3 ∧ {p | S ∈ p} ∈ P := by
  obtain ⟨q, hq⟩ := Ultrafilter.nonempty_of_mem hPQ.2
  refine ⟨{v | G.neighborSet v ∈ q}, ultrafilter_trace_cliqueFree G hG q, ?_⟩
  exact Filter.mem_of_superset hq (fun p hp => hp.2)

/-- A second symmetric ultrafilter extension of a countable `K₄`-free graph also
admits a countable triangle-free edge cover. -/
theorem countable_union_second_ultrafilterGraph_of_countable {V : Type} [Countable V]
    (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    IsCountableUnionOfTriangleFree
      (ultrafilterGraph (ultrafilterGraph G hG) (ultrafilterGraph_cliqueFree G hG)) := by
  classical
  let G₁ := ultrafilterGraph G hG
  let G₂ := ultrafilterGraph G₁ (ultrafilterGraph_cliqueFree G hG)
  have hex : ∀ P, (∃ Q, G₂.Adj P Q) →
      ∃ S : Set V, (G.induce S).CliqueFree 3 ∧ {p | S ∈ p} ∈ P := by
    rintro P ⟨Q, hPQ⟩
    exact second_ultrafilter_support G hG P Q hPQ
  let S : Ultrafilter (Ultrafilter V) → Set V := fun P =>
    if hP : ∃ Q, G₂.Adj P Q then (hex P hP).choose else ∅
  have hsupp : ∀ P, (∃ Q, G₂.Adj P Q) →
      (G.induce (S P)).CliqueFree 3 ∧ {p | S P ∈ p} ∈ P := by
    intro P hP
    have hSP : S P = (hex P hP).choose := dif_pos hP
    rw [hSP]
    exact (hex P hP).choose_spec
  have hcard : Cardinal.mk (Set V) ≤ Cardinal.mk (ℕ → Fin 2) := by
    simp only [Cardinal.mk_set, Cardinal.mk_arrow, Cardinal.mk_fin, Cardinal.mk_nat,
      Cardinal.lift_uzero, Nat.cast_ofNat]
    exact Cardinal.power_le_power_left (by simp) Cardinal.mk_le_aleph0
  let e : Set V ↪ (ℕ → Fin 2) :=
    (Cardinal.lift_mk_le'.mp (by simpa only [Cardinal.lift_uzero] using hcard)).some
  apply countable_union_of_triangle_free_fibers G₂ (fun P => e (S P))
  intro P Q R hPQ hPR hQR heq
  have hSP := hsupp P ⟨Q, hPQ⟩
  have hSQ := hsupp Q ⟨P, hPQ.symm⟩
  have hSR := hsupp R ⟨P, hPR.symm⟩
  have hSQP : S Q = S P := (e.injective heq.1).symm
  have hSRP : S R = S P := (e.injective heq.2).symm
  rw [hSQP] at hSQ
  rw [hSRP] at hSR
  have hU := ultrafilterGraph_support_cliqueFree G hG (S P) hSP.1
  have hUU := ultrafilterGraph_support_cliqueFree G₁
    (ultrafilterGraph_cliqueFree G hG) {p | S P ∈ p} hU
  exact hUU _ (SimpleGraph.is3Clique_triple_iff.mpr
    (show (G₂.induce {T | {p | S P ∈ p} ∈ T}).Adj ⟨P, hSP.2⟩ ⟨Q, hSQ.2⟩ ∧
      (G₂.induce {T | {p | S P ∈ p} ∈ T}).Adj ⟨P, hSP.2⟩ ⟨R, hSR.2⟩ ∧
      (G₂.induce {T | {p | S P ∈ p} ∈ T}).Adj ⟨Q, hSQ.2⟩ ⟨R, hSR.2⟩
      from ⟨hPQ, hPR, hQR⟩))

#print axioms ultrafilterGraph_support_cliqueFree
#print axioms second_ultrafilter_support
#print axioms countable_union_second_ultrafilterGraph_of_countable


/-- Directed Fubini extension commutes with a finite union of graphs. It need not
commute with a countable union. -/
theorem fubiniAdj_finite_iSup {V I : Type*} [Finite I]
    (H : I → SimpleGraph V) (p q : Ultrafilter V) :
    fubiniAdj (⨆ i, H i) p q ↔ ∃ i, fubiniAdj (H i) p q := by
  change (∀ᶠ a in (p : Filter V), ∀ᶠ b in (q : Filter V), (⨆ i, H i).Adj a b) ↔
    ∃ i, ∀ᶠ a in (p : Filter V), ∀ᶠ b in (q : Filter V), (H i).Adj a b
  simp_rw [SimpleGraph.iSup_adj, Ultrafilter.eventually_exists_iff]

private theorem no_three_fubini {V : Type*} (G : SimpleGraph V)
    (hG : G.CliqueFree 3) (p q r : Ultrafilter V)
    (hpq : fubiniAdj G p q) (hpr : fubiniAdj G p r) (hqr : fubiniAdj G q r) : False := by
  classical
  obtain ⟨a, haq, har⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem hpq hpr)
  obtain ⟨b, hab, hbr⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem haq hqr)
  obtain ⟨c, hac, hbc⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem har hbr)
  exact hG _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)

private theorem cliqueFree_three_of_ordered {V : Type*} [LinearOrder V]
    (G : SimpleGraph V)
    (hG : ∀ a b c, a < b → b < c → G.Adj a b → G.Adj a c → G.Adj b c → False) :
    G.CliqueFree 3 := by
  intro t ht
  let e : Fin 3 ↪o V := t.orderEmbOfFin ht.card_eq
  have hm : ∀ i, e i ∈ (t : Set V) := fun i => t.orderEmbOfFin_mem ht.card_eq i
  have he : ∀ i j, i ≠ j → G.Adj (e i) (e j) := by
    intro i j hij
    exact ht.isClique (hm i) (hm j) (fun h => hij (e.injective h))
  exact hG (e 0) (e 1) (e 2) (e.strictMono (by decide)) (e.strictMono (by decide))
    (he 0 1 (by decide)) (he 0 2 (by decide)) (he 1 2 (by decide))

/-- Symmetric ultrafilter extension does not increase the number of pieces in a
finite triangle-free edge cover. -/
theorem ultrafilterGraph_finite_cover {V I : Type*} [Finite I]
    (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (H : I → SimpleGraph V) (hH : ∀ i, (H i).CliqueFree 3) (hcov : G = ⨆ i, H i) :
    ∃ K : I → SimpleGraph (Ultrafilter V),
      (∀ i, (K i).CliqueFree 3) ∧ ultrafilterGraph G hG = ⨆ i, K i := by
  classical
  letI : LinearOrder (Ultrafilter V) := IsWellOrder.linearOrder WellOrderingRel
  let D : I → SimpleGraph (Ultrafilter V) := fun i =>
    { Adj := fun p q => (p < q ∧ fubiniAdj (H i) p q) ∨
        (q < p ∧ fubiniAdj (H i) q p)
      symm := fun _ _ h => h.symm
      loopless := fun p h => h.elim (fun h => (lt_irrefl p) h.1)
        (fun h => (lt_irrefl p) h.1) }
  have hD : ∀ i, (D i).CliqueFree 3 := by
    intro i
    apply cliqueFree_three_of_ordered
    intro p q r hpq hqr hpq' hpr' hqr'
    have hpr := hpq.trans hqr
    have h₁ : fubiniAdj (H i) p q := hpq'.elim And.right
      (fun h => (lt_asymm hpq h.1).elim)
    have h₂ : fubiniAdj (H i) p r := hpr'.elim And.right
      (fun h => (lt_asymm hpr h.1).elim)
    have h₃ : fubiniAdj (H i) q r := hqr'.elim And.right
      (fun h => (lt_asymm hqr h.1).elim)
    exact no_three_fubini (H i) (hH i) p q r h₁ h₂ h₃
  let K : I → SimpleGraph (Ultrafilter V) := fun i => ultrafilterGraph G hG ⊓ D i
  refine ⟨K, fun i => (hD i).anti inf_le_right, ?_⟩
  ext p q
  rw [SimpleGraph.iSup_adj]
  constructor
  · intro hpq
    rcases lt_or_gt_of_ne hpq.ne with hlt | hgt
    · have hf : fubiniAdj (⨆ i, H i) p q := hcov ▸ hpq.1
      obtain ⟨i, hi⟩ := (fubiniAdj_finite_iSup H p q).mp hf
      exact ⟨i, hpq, Or.inl ⟨hlt, hi⟩⟩
    · have hf : fubiniAdj (⨆ i, H i) q p := hcov ▸ hpq.2
      obtain ⟨i, hi⟩ := (fubiniAdj_finite_iSup H q p).mp hf
      exact ⟨i, hpq, Or.inr ⟨hgt, hi⟩⟩
  · rintro ⟨i, hi⟩
    exact hi.1

#print axioms fubiniAdj_finite_iSup
#print axioms ultrafilterGraph_finite_cover

/-- Triangle-free countable covers pull back along arbitrary graph homomorphisms. -/
theorem countable_union_of_hom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hH : IsCountableUnionOfTriangleFree H) :
    IsCountableUnionOfTriangleFree G := by
  obtain ⟨c, hc⟩ := (countable_union_iff_edge_coloring H).mp hH
  apply (countable_union_iff_edge_coloring G).mpr
  refine ⟨fun e => c (Sym2.map f e), ?_⟩
  intro a b d hab had hbd heq
  exact hc (f a) (f b) (f d) (f.map_rel hab) (f.map_rel had) (f.map_rel hbd) heq

/-- Removing equal-level edges makes an arbitrary graph countably vertex-colorable. -/
def levelGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph (V × ℕ) where
  Adj a b := G.Adj a.1 b.1 ∧ a.2 ≠ b.2
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := fun _ h => h.2 rfl

theorem levelGraph_cliqueFree {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    (levelGraph G).CliqueFree 4 := by
  classical
  by_contra h
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree h
  have he : ∀ i j : Fin 4, i ≠ j → G.Adj (e i).1 (e j).1 := by
    intro i j hij
    exact ((e.map_rel_iff).mpr hij).1
  exact no_adj_common_neighbors hG (he 0 1 (by decide)) (he 0 2 (by decide))
    (he 1 2 (by decide)) (he 0 3 (by decide)) (he 1 3 (by decide)) (he 2 3 (by decide))

def levelGraph_coloring {V : Type*} (G : SimpleGraph V) : (levelGraph G).Coloring ℕ :=
  SimpleGraph.Coloring.mk Prod.snd (fun h => h.2)

theorem countable_union_levelGraph {V : Type*} (G : SimpleGraph V) :
    IsCountableUnionOfTriangleFree (levelGraph G) := by
  let f : ℕ ↪ (ℕ → Fin 2) :=
    ⟨fun n i => if i = n then 1 else 0, by
      intro n m h
      by_contra hnm
      have h' := congrFun h n
      simp [hnm] at h'⟩
  exact countable_union_of_coloring _ ((levelGraph G).recolorOfEmbedding f (levelGraph_coloring G))

noncomputable def fiberUltrafilter {V : Type*} (v : V) : Ultrafilter (V × ℕ) :=
  Ultrafilter.map (fun n => (v, n)) (Filter.hyperfilter ℕ)

theorem fubiniAdj_fiberUltrafilter {V : Type*} (G : SimpleGraph V) (v w : V) :
    fubiniAdj (levelGraph G) (fiberUltrafilter v) (fiberUltrafilter w) ↔ G.Adj v w := by
  change {n : ℕ | {m : ℕ | G.Adj v w ∧ n ≠ m} ∈ Filter.hyperfilter ℕ} ∈
    Filter.hyperfilter ℕ ↔ G.Adj v w
  have hi : ∀ n : ℕ, {m : ℕ | G.Adj v w ∧ n ≠ m} ∈ Filter.hyperfilter ℕ ↔ G.Adj v w := by
    intro n
    constructor
    · intro h
      obtain ⟨m, hm⟩ := Ultrafilter.nonempty_of_mem h
      exact hm.1
    · intro h
      have hn := (Set.finite_singleton n).compl_mem_hyperfilter
      exact Filter.mem_of_superset hn (fun m hm => ⟨h, Ne.symm hm⟩)
  simp only [hi]
  exact Filter.eventually_const

/-- Every `K₄`-free graph maps into the ultrafilter extension of a countably
vertex-colorable `K₄`-free graph. -/
noncomputable def fiberUltrafilterHom {V : Type*} (G : SimpleGraph V)
    (hG : G.CliqueFree 4) :
    G →g ultrafilterGraph (levelGraph G) (levelGraph_cliqueFree G hG) where
  toFun := fiberUltrafilter
  map_rel' h := ⟨(fubiniAdj_fiberUltrafilter G _ _).mpr h,
    (fubiniAdj_fiberUltrafilter G _ _).mpr h.symm⟩

/-- Thus a hypothetical witness can be recovered from a coverable base by one
ultrafilter extension. This is a reduction, not an existence theorem. -/
theorem no_cover_ultrafilter_levelGraph {V : Type*} (G : SimpleGraph V)
    (hG : G.CliqueFree 4) (h : ¬IsCountableUnionOfTriangleFree G) :
    ¬IsCountableUnionOfTriangleFree
      (ultrafilterGraph (levelGraph G) (levelGraph_cliqueFree G hG)) := by
  exact fun hcov => h (countable_union_of_hom (fiberUltrafilterHom G hG) hcov)

#print axioms countable_union_of_hom
#print axioms levelGraph_cliqueFree
#print axioms countable_union_levelGraph
#print axioms fubiniAdj_fiberUltrafilter
#print axioms no_cover_ultrafilter_levelGraph

/-- A diagonal binary sequence avoiding the color class at each coordinate. -/
noncomputable def diagonalBits (g : (ℕ → Fin 2) → ℕ) (n : ℕ) : Fin 2 := by
  classical
  exact if ∃ x : ℕ → Fin 2, g x = n ∧
      (∀ k, ∀ hk : k < n, x k = diagonalBits g k) ∧ x n = 0 then 1 else 0
termination_by n

/-- Unlike its restriction to a triangle-free binary-encoded graph, the full
first-difference labeling has no adapted vertex labeling. -/
theorem firstDifference_no_adapted (g : (ℕ → Fin 2) → ℕ) :
    ∃ x y : ℕ → Fin 2, x ≠ y ∧
      g x = firstDifference id Function.injective_id x y ∧
      g y = firstDifference id Function.injective_id x y := by
  classical
  let t := diagonalBits g
  let n := g t
  by_cases h : ∃ x : ℕ → Fin 2, g x = n ∧ (∀ k, ∀ hk : k < n, x k = t k) ∧ x n = 0
  · have ht : t n = 1 := by
      change diagonalBits g n = 1
      rw [diagonalBits]
      exact if_pos h
    obtain ⟨x, hgx, hx, hxn⟩ := h
    have hne : x ≠ t := by
      intro hxt
      have := congrFun hxt n
      rw [hxn, ht] at this
      exact Fin.zero_ne_one this
    have hd : firstDifference id Function.injective_id x t = n := by
      apply firstDifference_eq_of_bits id Function.injective_id hne
      · change x n ≠ t n
        rw [hxn, ht]
        decide
      · exact hx
    exact ⟨x, t, hne, hgx.trans hd.symm, hd.symm⟩
  · have ht : t n = 0 := by
      change diagonalBits g n = 0
      rw [diagonalBits]
      exact if_neg h
    exact (h ⟨t, rfl, fun _ _ => rfl, ht⟩).elim

/-- The usual shift graph on increasing pairs of an ordered type. -/
def orderedShiftGraph (A : Type*) [LinearOrder A] : SimpleGraph {p : A × A // p.1 < p.2} where
  Adj a b := a.1.2 = b.1.1 ∨ b.1.2 = a.1.1
  symm := fun _ _ h => h.symm
  loopless := fun a h => h.elim (fun h => (ne_of_lt a.2) h.symm)
    (fun h => (ne_of_lt a.2) h.symm)

theorem orderedShiftGraph_cliqueFree (A : Type*) [LinearOrder A] :
    (orderedShiftGraph A).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp ht
  have ha := a.2
  have hb := b.2
  have hc := c.2
  change a.1.2 = b.1.1 ∨ b.1.2 = a.1.1 at hab
  change a.1.2 = c.1.1 ∨ c.1.2 = a.1.1 at hac
  change b.1.2 = c.1.1 ∨ c.1.2 = b.1.1 at hbc
  rcases hab with hab | hab <;> rcases hac with hac | hac <;>
    rcases hbc with hbc | hbc <;> order

/-- A coloring of the shift graph injects its index order into the power set
of the color type. -/
theorem orderedShiftGraph_coloring_injection {A C : Type*} [LinearOrder A]
    (f : (orderedShiftGraph A).Coloring C) : Nonempty (A ↪ Set C) := by
  classical
  let S : A → Set C := fun b => {i | ∃ a, ∃ h : a < b, f ⟨(a, b), h⟩ = i}
  have hlt : ∀ a b, a < b → S a ≠ S b := by
    intro a b hab hS
    have hi : f ⟨(a, b), hab⟩ ∈ S b := ⟨a, hab, rfl⟩
    rw [← hS] at hi
    obtain ⟨d, hd, heq⟩ := hi
    exact f.valid (show (orderedShiftGraph A).Adj ⟨(d, a), hd⟩ ⟨(a, b), hab⟩
      from Or.inl rfl) heq
  refine ⟨⟨S, ?_⟩⟩
  intro a b hS
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hlt a b h hS
  · exact hlt b a h hS.symm

universe u

/-- Triangle-free graphs have arbitrarily large vertex chromatic cardinal. -/
theorem exists_triangleFree_not_colorable (C : Type u) :
    ∃ (V : Type u) (G : SimpleGraph V), G.CliqueFree 3 ∧ IsEmpty (G.Coloring C) := by
  classical
  let A := Set (Set C)
  letI : LinearOrder A := IsWellOrder.linearOrder WellOrderingRel
  refine ⟨_, orderedShiftGraph A, orderedShiftGraph_cliqueFree A, ⟨?_⟩⟩
  intro f
  obtain ⟨e⟩ := orderedShiftGraph_coloring_injection f
  exact Function.cantor_injective e e.injective

/-- The unrestricted adapted-labeling lemma for triangle-free graphs is false.
This does not disprove Erdős Problem 595: it only rules out one proposed approach. -/
theorem exists_triangleFree_no_adapted :
    ∃ (V : Type) (G : SimpleGraph V) (c : Sym2 V → ℕ), G.CliqueFree 3 ∧
      ∀ g : V → ℕ, ∃ a b, G.Adj a b ∧ g a = c s(a, b) ∧ g b = c s(a, b) := by
  classical
  let X := ℕ → Fin 2
  obtain ⟨B, G, hG, hcG⟩ := exists_triangleFree_not_colorable (X → ℕ)
  let H := G.comap (Prod.fst : B × X → B)
  let c : Sym2 (B × X) → ℕ := Sym2.lift
    ⟨fun a b => firstDifference id Function.injective_id a.2 b.2,
      fun a b => firstDifference_symm id Function.injective_id a.2 b.2⟩
  have hH : H.CliqueFree 3 := by
    intro t ht
    obtain ⟨a, b, d, hab, had, hbd, _⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact hG _ (SimpleGraph.is3Clique_triple_iff.mpr
      (show G.Adj a.1 b.1 ∧ G.Adj a.1 d.1 ∧ G.Adj b.1 d.1 from ⟨hab, had, hbd⟩))
  refine ⟨B × X, H, c, hH, ?_⟩
  intro g
  by_contra h
  have hf : ∀ v w, G.Adj v w → (fun x : X => g (v, x)) ≠ (fun x : X => g (w, x)) := by
    intro v w hvw heq
    obtain ⟨x, y, _, hx, hy⟩ := firstDifference_no_adapted (fun x => g (v, x))
    apply h
    refine ⟨(v, x), (w, y), hvw, hx, ?_⟩
    change g (w, y) = firstDifference id Function.injective_id x y
    rw [← congrFun heq y]
    exact hy
  exact hcG.false (SimpleGraph.Coloring.mk (fun v (x : X) => g (v, x)) (fun h => hf _ _ h))

#print axioms firstDifference_no_adapted
#print axioms orderedShiftGraph_cliqueFree
#print axioms orderedShiftGraph_coloring_injection
#print axioms exists_triangleFree_not_colorable
#print axioms exists_triangleFree_no_adapted

/-- Exact reduction: a universal negative answer is equivalent to coverability
of ultrafilter extensions of countably vertex-colorable `K₄`-free graphs. -/
theorem all_cover_iff_countably_colorable_ultrafilter_cover :
    (∀ (V : Type u) (G : SimpleGraph V), G.CliqueFree 4 → IsCountableUnionOfTriangleFree G) ↔
    (∀ (V : Type u) (G : SimpleGraph V) (hG : G.CliqueFree 4),
      Nonempty (G.Coloring ℕ) → IsCountableUnionOfTriangleFree (ultrafilterGraph G hG)) := by
  constructor
  · intro h V G hG _
    exact h _ _ (ultrafilterGraph_cliqueFree G hG)
  · intro h V G hG
    exact countable_union_of_hom (fiberUltrafilterHom G hG)
      (h _ (levelGraph G) (levelGraph_cliqueFree G hG) ⟨levelGraph_coloring G⟩)

#print axioms all_cover_iff_countably_colorable_ultrafilter_cover

/-- Fubini adjacency is preserved by pushing both ultrafilters forward along a
homomorphism of the original graphs. -/
theorem fubiniAdj_map_hom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) {p q : Ultrafilter V} (h : fubiniAdj G p q) :
    fubiniAdj H (Ultrafilter.map f p) (Ultrafilter.map f q) := by
  change {a | {b | H.Adj (f a) (f b)} ∈ q} ∈ p
  apply Filter.mem_of_superset h
  intro a ha
  exact Filter.mem_of_superset ha (fun b hb => f.map_rel hb)

/-- Symmetric ultrafilter extension is functorial on `K₄`-free graphs. -/
def ultrafilterGraphHom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.CliqueFree 4) (hH : H.CliqueFree 4) (f : G →g H) :
    ultrafilterGraph G hG →g ultrafilterGraph H hH where
  toFun := Ultrafilter.map f
  map_rel' h := ⟨fubiniAdj_map_hom f h.1, fubiniAdj_map_hom f h.2⟩

/-- A continuum-sized ordinary vertex palette suffices for the extension of a
countable `K₄`-free graph. -/
theorem binary_coloring_ultrafilterGraph_of_countable {W : Type} [Countable W]
    (H : SimpleGraph W) (hH : H.CliqueFree 4) :
    Nonempty ((ultrafilterGraph H hH).Coloring (ℕ → Fin 2)) := by
  classical
  have hcard : Cardinal.mk (Set W) ≤ Cardinal.mk (ℕ → Fin 2) := by
    simp only [Cardinal.mk_set, Cardinal.mk_arrow, Cardinal.mk_fin, Cardinal.mk_nat,
      Cardinal.lift_uzero, Nat.cast_ofNat]
    exact Cardinal.power_le_power_left (by simp) Cardinal.mk_le_aleph0
  let e : Set W ↪ (ℕ → Fin 2) :=
    (Cardinal.lift_mk_le'.mp (by simpa only [Cardinal.lift_uzero] using hcard)).some
  exact ⟨(ultrafilterGraph H hH).recolorOfEmbedding e
    (ultrafilterGraph_trace_coloring H hH).some⟩

/-- A homomorphism to a countable `K₄`-free target suffices for coverability
of the ultrafilter extension. Proper countable vertex colorability alone does not
supply such a target. -/
theorem countable_union_ultrafilterGraph_of_countable_target {V : Type*} {W : Type}
    [Countable W] {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.CliqueFree 4) (hH : H.CliqueFree 4) (f : G →g H) :
    IsCountableUnionOfTriangleFree (ultrafilterGraph G hG) := by
  exact countable_union_of_hom (ultrafilterGraphHom hG hH f)
    (countable_union_ultrafilterGraph_of_countable H hH)

theorem levelGraph_triangleFree {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    (levelGraph G).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨a, b, d, hab, had, hbd, _⟩ := SimpleGraph.is3Clique_iff.mp ht
  exact hG _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab.1, had.1, hbd.1⟩)

/-- Even a countably vertex-colorable triangle-free graph need not admit a
homomorphism to any countable `K₄`-free graph. -/
theorem exists_countably_colorable_no_countable_cliqueFree_target :
    ∃ (V : Type) (G : SimpleGraph V), G.CliqueFree 3 ∧ Nonempty (G.Coloring ℕ) ∧
      ∀ (W : Type) (_ : Countable W) (H : SimpleGraph W), H.CliqueFree 4 → IsEmpty (G →g H) := by
  classical
  obtain ⟨V, G, hG, hcolor⟩ := exists_triangleFree_not_colorable (ℕ → Fin 2)
  have hG₄ : G.CliqueFree 4 := hG.mono (by omega)
  refine ⟨V × ℕ, levelGraph G, levelGraph_triangleFree G hG,
    ⟨levelGraph_coloring G⟩, ?_⟩
  intro W hW H hH
  refine ⟨fun f => ?_⟩
  let F := (ultrafilterGraphHom (levelGraph_cliqueFree G hG₄) hH f).comp
    (fiberUltrafilterHom G hG₄)
  obtain ⟨c⟩ := binary_coloring_ultrafilterGraph_of_countable H hH
  exact hcolor.false (c.comp F)

#print axioms fubiniAdj_map_hom
#print axioms ultrafilterGraphHom
#print axioms binary_coloring_ultrafilterGraph_of_countable
#print axioms countable_union_ultrafilterGraph_of_countable_target
#print axioms exists_countably_colorable_no_countable_cliqueFree_target

/-- Adjoin a universal vertex, represented by `none`. -/
def coneGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj
    | none, none => False
    | some a, some b => G.Adj a b
    | _, _ => True
  symm := by
    intro a b h
    cases a <;> cases b <;> simp_all [G.adj_comm]
  loopless := by
    intro a h
    cases a <;> simp_all

theorem coneGraph_cliqueFree {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    (coneGraph G).CliqueFree 4 := by
  classical
  have h₃ : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → False := by
    intro a b c hab hac hbc
    exact hG _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)
  have h₄ : ∀ a b c d, (coneGraph G).Adj a b → (coneGraph G).Adj a c →
      (coneGraph G).Adj a d → (coneGraph G).Adj b c → (coneGraph G).Adj b d →
      (coneGraph G).Adj c d → False := by
    intro a b c d
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp only [coneGraph] <;> aesop
  by_contra h
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree h
  have he : ∀ i j : Fin 4, i ≠ j → (coneGraph G).Adj (e i) (e j) :=
    fun i j h => e.map_rel_iff.mpr h
  exact h₄ (e 0) (e 1) (e 2) (e 3) (he 0 1 (by decide)) (he 0 2 (by decide))
    (he 0 3 (by decide)) (he 1 2 (by decide)) (he 1 3 (by decide)) (he 2 3 (by decide))

/-- A cone over a triangle-free graph is the union of two triangle-free graphs. -/
theorem coneGraph_two_pieces {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    ∃ B S : SimpleGraph (Option V), B.CliqueFree 3 ∧ S.CliqueFree 3 ∧ coneGraph G = B ⊔ S := by
  classical
  let B : SimpleGraph (Option V) :=
    { Adj := fun a b => match a, b with
        | some v, some w => G.Adj v w
        | _, _ => False
      symm := by intro a b h; cases a <;> cases b <;> simp_all [G.adj_comm]
      loopless := by intro a h; cases a <;> simp_all }
  let f : Option V → Fin 2 := fun a => a.elim 0 (fun _ => 1)
  let S := (⊤ : SimpleGraph (Fin 2)).comap f
  have hB : B.CliqueFree 3 := by
    intro t ht
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp ht
    cases a with
    | none => cases b <;> exact hab.elim
    | some a =>
      cases b with
      | none => exact hab.elim
      | some b =>
        cases c with
        | none => exact hac.elim
        | some c => exact hG _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)
  have hS : S.CliqueFree 3 := by
    have hc : S.Colorable 2 := ⟨SimpleGraph.Coloring.mk f (fun h => h)⟩
    exact hc.cliqueFree (by omega)
  refine ⟨B, S, hB, hS, ?_⟩
  ext a b
  cases a <;> cases b <;> simp [coneGraph, B, S, f]

theorem countable_union_coneGraph {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    IsCountableUnionOfTriangleFree (coneGraph G) := by
  obtain ⟨B, S, hB, hS, hcov⟩ := coneGraph_two_pieces G hG
  refine ⟨fun n => if n = 0 then B else S, fun n => ?_, ?_⟩
  · dsimp only
    split_ifs <;> assumption
  · rw [hcov]
    ext a b
    simp only [SimpleGraph.sup_adj, SimpleGraph.iSup_adj]
    constructor
    · rintro (h | h)
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    · rintro ⟨n, hn⟩
      by_cases h : n = 0
      · exact Or.inl (by simpa only [if_pos h] using hn)
      · exact Or.inr (by simpa only [if_neg h] using hn)

/-- Failure of extension of a prescribed coloring can occur in a graph that
nevertheless admits even a two-piece triangle-free cover. Hence such failure
alone is not an obstruction of the kind demanded in Erdős Problem 595. -/
theorem exists_nonextendable_coloring_of_coverable_cone :
    ∃ (V : Type) (G : SimpleGraph V) (c : Sym2 V → ℕ), G.CliqueFree 3 ∧
      (coneGraph G).CliqueFree 4 ∧ IsCountableUnionOfTriangleFree (coneGraph G) ∧
      ∀ d : Sym2 (Option V) → ℕ,
        (∀ a b, G.Adj a b → d s(some a, some b) = c s(a, b)) →
        ∃ a b t, (coneGraph G).Adj a b ∧ (coneGraph G).Adj a t ∧
          (coneGraph G).Adj b t ∧ d s(a, b) = d s(a, t) ∧ d s(a, b) = d s(b, t) := by
  obtain ⟨V, G, c, hG, hc⟩ := exists_triangleFree_no_adapted
  refine ⟨V, G, c, hG, coneGraph_cliqueFree G hG, countable_union_coneGraph G hG, ?_⟩
  intro d hd
  obtain ⟨a, b, hab, ha, hb⟩ := hc (fun v => d s(none, some v))
  exact ⟨none, some a, some b, True.intro, True.intro, hab,
    ha.trans hb.symm, ha.trans (hd a b hab).symm⟩

#print axioms coneGraph_cliqueFree
#print axioms coneGraph_two_pieces
#print axioms countable_union_coneGraph
#print axioms exists_nonextendable_coloring_of_coverable_cone

end Erdos595Work
