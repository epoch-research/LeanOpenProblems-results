import FormalConjecturesUtil

/-!
# The Erdős–Sós edge threshold for bipartite hosts

This file proves the bipartite-host case, not the unrestricted Erdős–Sós
conjecture. It is independent of `Submission.Spec`, `Submission.Auxiliary`, and
`Submission.Critical`.

The proof combines a vertex-weighted peeling lemma with a color-preserving
leaf induction for finite trees. All copies are ordinary (not induced) copies.
-/

open SimpleGraph
open scoped BigOperators

namespace Erdos548.Bipartite

universe u v

section GreedyEmbedding

private theorem bool_eq_of_ne_same {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) :
    a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Restricting the source vertices cannot enlarge a color class. -/
theorem card_restrict_color_ne_le {A : Type u} [Fintype A]
    (s : Set A) [Fintype s] (c : A → Bool) (b : Bool) :
    Fintype.card {x : s // c x ≠ b} ≤ Fintype.card {x : A // c x ≠ b} := by
  apply Fintype.card_le_of_injective (fun x => (⟨x.val.val, x.property⟩ : {x : A // c x ≠ b}))
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : {x : A // c x ≠ b} => z.val) h

/-- Deleting a vertex in the class strictly decreases that class's cardinality. -/
theorem card_restrict_color_ne_lt {A : Type u} [Fintype A]
    (s : Set A) [Fintype s] (c : A → Bool) (b : Bool) {x : A}
    (hx : x ∉ s) (hc : c x ≠ b) :
    Fintype.card {y : s // c y ≠ b} < Fintype.card {y : A // c y ≠ b} := by
  apply Fintype.card_lt_of_injective_of_notMem
    (fun y : {y : s // c y ≠ b} => (⟨y.val.val, y.property⟩ : {y : A // c y ≠ b}))
    (fun y z h => Subtype.ext (Subtype.ext
      (congrArg (fun z : {x : A // c x ≠ b} => z.val) h)))
    (b := ⟨x, hc⟩)
  rintro ⟨y, hy⟩
  have hy' : y.val.val = x := congrArg (fun z : {y : A // c y ≠ b} => z.val) hy
  exact hx (hy' ▸ y.val.property)

/-- Only already used vertices of the opposite color can obstruct a new
neighbor. The map of already used vertices need not be injective. -/
theorem exists_adj_fresh_of_coloring {A : Type u} {V : Type v}
    [Fintype A] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : A → Bool) (d : G.Coloring Bool) (f : A → V)
    (hf : ∀ x, d (f x) = c x) (v : V)
    (hdeg : Fintype.card {x : A // c x ≠ d v} < G.degree v) :
    ∃ w, G.Adj v w ∧ ∀ x, f x ≠ w := by
  classical
  by_contra! h
  let used : Finset A := Finset.univ.filter (fun x => c x ≠ d v)
  have hsub : G.neighborFinset v ⊆ used.image f := by
    intro w hw
    have hadj := (G.mem_neighborFinset _ _).mp hw
    obtain ⟨x, hx⟩ := h w hadj
    refine Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hx⟩
    rw [← hf x, hx]
    exact (d.valid hadj).symm
  have hle := Finset.card_le_card hsub
  have hcard : (used.image f).card ≤ Fintype.card {x : A // c x ≠ d v} := by
    calc
      (used.image f).card ≤ used.card := Finset.card_image_le
      _ = Fintype.card {x : A // c x ≠ d v} := (Fintype.card_subtype _).symm
  rw [G.card_neighborFinset_eq_degree] at hle
  omega

/-- A finite tree embeds respecting the two given colorings if each host vertex
has at least as many neighbors as the entire opposite target color class.
Both colors must occur in the host; this includes the one-vertex target case.
The degree bounds may be stronger than needed for any intermediate subtree. -/
theorem exists_color_preserving_copy_of_degree
    {A : Type u} {V : Type v} [Fintype A] [Fintype V]
    (T : SimpleGraph A) (G : SimpleGraph V) [DecidableRel G.Adj]
    (cT : T.Coloring Bool) (cG : G.Coloring Bool) (hT : T.IsTree)
    (hsurj : Function.Surjective cG)
    (hG : ∀ w, Fintype.card {x : A // cT x ≠ cG w} ≤ G.degree w) :
    ∃ f : T.Copy G, ∀ x, cG (f x) = cT x := by
  classical
  suffices main : ∀ n : ℕ, ∀ {B : Type u} [Fintype B], Fintype.card B = n →
      ∀ (R : SimpleGraph B) (cR : R.Coloring Bool), R.IsTree →
        (∀ w, Fintype.card {x : B // cR x ≠ cG w} ≤ G.degree w) →
          ∃ f : R.Copy G, ∀ x, cG (f x) = cR x by
    exact main _ rfl T cT hT hG
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro B _ hn R cR hR hdegree
    by_cases hsmall : Fintype.card B ≤ 1
    · letI : Subsingleton B := Fintype.card_le_one_iff_subsingleton.mp hsmall
      obtain ⟨x₀⟩ := hR.isConnected.nonempty
      obtain ⟨w, hw⟩ := hsurj (cR x₀)
      refine ⟨{
        toHom := { toFun := fun _ => w, map_rel' := ?_ }
        injective' := fun _ _ _ => Subsingleton.elim _ _ }, ?_⟩
      · intro x y hxy
        exact (hxy.ne (Subsingleton.elim x y)).elim
      · intro x
        simpa only [Subsingleton.elim x x₀] using hw
    · letI : Nontrivial B := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨leaf, hleaf⟩ := hR.exists_vert_degree_one_of_nontrivial
      let s : Set B := {leaf}ᶜ
      have hs_card : Fintype.card s = n - 1 := by
        dsimp [s]
        rw [Fintype.card_compl_set]
        simp [hn]
      have hs_lt : Fintype.card s < n := by omega
      have hs_tree : (R.induce s).IsTree :=
        ⟨hR.isConnected.induce_compl_singleton_of_degree_eq_one hleaf,
          hR.IsAcyclic.induce s⟩
      let cS : (R.induce s).Coloring Bool :=
        Coloring.mk (fun x => cR x) (fun h => cR.valid h)
      obtain ⟨f, hf⟩ := ih (Fintype.card s) hs_lt rfl (R.induce s) cS hs_tree
        (fun w => (card_restrict_color_ne_le s cR (cG w)).trans (hdegree w))
      obtain ⟨parent, hadj, hparent⟩ :=
        SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hleaf
      have hp : parent ≠ leaf := hadj.ne.symm
      let p : s := ⟨parent, hp⟩
      have hc : cR leaf ≠ cG (f p) := by
        rw [hf p]
        exact cR.valid hadj
      have hlt : Fintype.card {x : s // cS x ≠ cG (f p)} < G.degree (f p) :=
        (card_restrict_color_ne_lt s cR (cG (f p)) (by simp [s]) hc).trans_le
          (hdegree (f p))
      obtain ⟨w, hw, hfresh⟩ := exists_adj_fresh_of_coloring G cS cG f hf (f p) hlt
      let g : B → V := fun x => if hx : x = leaf then w else f ⟨x, hx⟩
      let f' : R.Copy G := by
        refine { toHom := { toFun := g, map_rel' := ?_ }, injective' := ?_ }
        · intro x y hxy
          by_cases hx : x = leaf
          · subst x
            have hy : y = parent := hparent y hxy
            subst y
            simpa [g, p, hp] using hw.symm
          · by_cases hy : y = leaf
            · subst y
              have hx' : x = parent := hparent x hxy.symm
              subst x
              simpa [g, p, hp] using hw
            · exact (show G.Adj (g x) (g y) from by
                simpa only [g, dif_neg hx, dif_neg hy] using
                  f.toHom.map_rel (show (R.induce s).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy))
        · intro x y hxy
          change g x = g y at hxy
          by_cases hx : x = leaf
          · by_cases hy : y = leaf
            · exact hx.trans hy.symm
            · have heq : w = f ⟨y, hy⟩ := by simpa [g, hx, hy] using hxy
              exact (hfresh ⟨y, hy⟩ heq.symm).elim
          · by_cases hy : y = leaf
            · have heq : f ⟨x, hx⟩ = w := by simpa [g, hx, hy] using hxy
              exact (hfresh ⟨x, hx⟩ heq).elim
            · have heq : f ⟨x, hx⟩ = f ⟨y, hy⟩ := by
                simpa only [g, dif_neg hx, dif_neg hy] using hxy
              exact congrArg Subtype.val (f.injective heq)
      refine ⟨f', ?_⟩
      intro x
      change cG (g x) = cR x
      by_cases hx : x = leaf
      · subst x
        simpa only [g, dif_pos rfl] using bool_eq_of_ne_same (cG.valid hw).symm hc
      · simpa only [g, dif_neg hx] using hf ⟨x, hx⟩

end GreedyEmbedding

section WeightedCore

/-- Enumeration-independent degree agrees with mathlib's finite degree. -/
theorem ncard_neighborSet_eq_degree {V : Type v} (G : SimpleGraph V) (x : V)
    [Fintype (G.neighborSet x)] : (G.neighborSet x).ncard = G.degree x :=
  (Set.ncard_eq_toFinset_card' _).trans (G.card_neighborFinset_eq_degree x)

/-- Transport enumeration-independent degrees along an isomorphism. -/
theorem neighborSet_ncard_iso {A : Type u} {V : Type v}
    {G : SimpleGraph A} {H : SimpleGraph V} (e : G ≃g H) (x : A) :
    (H.neighborSet (e x)).ncard = (G.neighborSet x).ncard :=
  (Set.ncard_congr' (e.mapNeighborSet x)).symm

/-- The exact one-vertex deletion identity: every removed edge is charged once. -/
theorem edge_ncard_delete_vertex {V : Type v} [Finite V]
    (G : SimpleGraph V) (x : V) :
    (G.induce {x}ᶜ).edgeSet.ncard + (G.neighborSet x).ncard = G.edgeSet.ncard := by
  classical
  letI := Fintype.ofFinite V
  rw [ncard_neighborSet_eq_degree]
  have h : (G.induce {x}ᶜ).edgeFinset.card + G.degree x = G.edgeFinset.card := by
    rw [G.card_edgeFinset_induce_compl_singleton, G.card_edgeFinset_deleteIncidenceSet]
    exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset x)
  simpa only [Set.ncard_eq_toFinset_card', SimpleGraph.edgeFinset] using h

/-- Flatten two successive restrictions. This definition is copied, not imported,
from the elementary induced-subgraph infrastructure in `Critical.lean`. -/
noncomputable def induceInduceIso {V : Type v} (G : SimpleGraph V)
    (s : Set V) (t : Set s) :
    (G.induce s).induce t ≃g G.induce (Subtype.val '' t) where
  toEquiv := Equiv.Set.image (Subtype.val : s → V) t Subtype.val_injective
  map_rel_iff' := by intro x y; rfl

/-- Weighted peeling. If the number of edges exceeds the sum of nonnegative
integer vertex costs, some nonempty induced subgraph has degree strictly larger
than the cost at every vertex. No bipartiteness assumption is required here. -/
theorem exists_weighted_core {V : Type v} [Fintype V]
    (G : SimpleGraph V) (cost : V → ℕ)
    (hG : (∑ x, cost x) < G.edgeSet.ncard) :
    ∃ s : Set V, s.Nonempty ∧
      ∀ x : s, cost x < ((G.induce s).neighborSet x).ncard := by
  classical
  suffices main : ∀ n : ℕ, ∀ {B : Type v} [Fintype B], Fintype.card B = n →
      ∀ (H : SimpleGraph B) (w : B → ℕ), (∑ x, w x) < H.edgeSet.ncard →
        ∃ s : Set B, s.Nonempty ∧
          ∀ x : s, w x < ((H.induce s).neighborSet x).ncard by
    exact main _ rfl G cost hG
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro B _ hn H w hpos
    have hnonempty : Nonempty B := by
      by_contra he
      letI : IsEmpty B := not_nonempty_iff.mp he
      have hbot : H = ⊥ := Subsingleton.elim _ _
      simp [hbot] at hpos
    letI : Nonempty B := hnonempty
    by_cases hall : ∀ x, w x < (H.neighborSet x).ncard
    · refine ⟨Set.univ, Set.univ_nonempty, ?_⟩
      intro x
      rw [← neighborSet_ncard_iso H.induceUnivIso x]
      exact hall x
    · push_neg at hall
      obtain ⟨x, hx⟩ := hall
      let s : Set B := {x}ᶜ
      have hs_card : Fintype.card s = n - 1 := by
        dsimp [s]
        rw [Fintype.card_compl_set]
        simp [hn]
      have hs_lt : Fintype.card s < n := by
        have := Fintype.card_pos_iff.mpr hnonempty
        omega
      have he := edge_ncard_delete_vertex H x
      have hw : (∑ y : s, w y) + w x = ∑ y, w y := by
        have hsum : (∑ y ∈ Finset.univ.erase x, w y) = ∑ y : s, w y :=
          Finset.sum_subtype _ (fun y => by simp [s]) _
        rw [← hsum]
        exact Finset.sum_erase_add Finset.univ w (Finset.mem_univ x)
      have hsmaller : (∑ y : s, w y) < (H.induce s).edgeSet.ncard := by
        change (H.induce s).edgeSet.ncard + (H.neighborSet x).ncard = _ at he
        omega
      obtain ⟨t, ht, hdegree⟩ := ih _ hs_lt rfl (H.induce s) (fun y => w y) hsmaller
      refine ⟨Subtype.val '' t, ht.image _, ?_⟩
      intro z
      let e := induceInduceIso H s t
      obtain ⟨y, rfl⟩ := e.toEquiv.surjective z
      change w (e y).val < ((H.induce (Subtype.val '' t)).neighborSet (e y)).ncard
      rw [neighborSet_ncard_iso e y]
      exact hdegree y

end WeightedCore

section BipartiteThreshold

/-- Mathlib's two-colorability supplies a Boolean coloring, covering every
vertex (including isolated vertices) by exactly one of the two classes. -/
theorem exists_bool_coloring {V : Type v} (G : SimpleGraph V) (hG : G.IsBipartite) :
    Nonempty (G.Coloring Bool) := by
  obtain ⟨c⟩ := hG
  exact ⟨Coloring.mk (fun x => finTwoEquiv (c x))
    (fun h he => c.valid h (finTwoEquiv.injective he))⟩

/-- The endpoints of one edge witness both colors in a Boolean coloring. -/
theorem coloring_surjective_of_adj {V : Type v} {G : SimpleGraph V}
    (c : G.Coloring Bool) {x y : V} (hxy : G.Adj x y) : Function.Surjective c := by
  intro b
  by_cases hx : c x = b
  · exact ⟨x, hx⟩
  · exact ⟨y, bool_eq_of_ne_same (c.valid hxy).symm (Ne.symm hx)⟩

/-- Every proper two-coloring of a nontrivial finite tree uses both colors. -/
theorem coloring_surjective_of_isTree {A : Type u} [Finite A] [Nontrivial A]
    {T : SimpleGraph A} (c : T.Coloring Bool) (hT : T.IsTree) :
    Function.Surjective c := by
  classical
  letI := Fintype.ofFinite A
  obtain ⟨x, hx⟩ := hT.exists_vert_degree_one_of_nontrivial
  obtain ⟨y, hxy⟩ := (T.degree_pos_iff_exists_adj x).mp (by omega)
  exact coloring_surjective_of_adj c hxy

/-- The two opposite-color classes partition the whole finite vertex type. -/
theorem opposite_color_card_add {A : Type u} [Fintype A] (c : A → Bool) (b : Bool) :
    Fintype.card {x : A // c x ≠ b} + Fintype.card {x : A // c x ≠ !b} =
      Fintype.card A := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun x : A => c x = true)
    (fun _ => (1 : ℕ))
  cases b <;> simpa [add_comm] using h

/-- Surjectivity makes both opposite-color classes nonempty. -/
theorem opposite_color_card_pos {A : Type u} [Fintype A] (c : A → Bool)
    (hc : Function.Surjective c) (b : Bool) :
    0 < Fintype.card {x : A // c x ≠ b} := by
  apply Fintype.card_pos_iff.mpr
  obtain ⟨x, hx⟩ := hc (!b)
  exact ⟨⟨x, by rw [hx]; exact Bool.not_ne_self b⟩⟩

/-- A `Finite`-only, enumeration-independent form of the greedy embedding
lemma. The degree threshold is the size of the opposite target color class. -/
theorem exists_color_preserving_copy_of_neighborSet_ncard
    {A : Type u} {V : Type v} [Finite A] [Finite V]
    (T : SimpleGraph A) (G : SimpleGraph V)
    (cT : T.Coloring Bool) (cG : G.Coloring Bool) (hT : T.IsTree)
    (hsurj : Function.Surjective cG)
    (hG : ∀ w, Nat.card {x : A // cT x ≠ cG w} ≤ (G.neighborSet w).ncard) :
    ∃ f : T.Copy G, ∀ x, cG (f x) = cT x := by
  classical
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite V
  apply exists_color_preserving_copy_of_degree T G cT cG hT hsurj
  intro w
  simpa only [Nat.card_eq_fintype_card, ncard_neighborSet_eq_degree] using hG w

/-- A positive weighted edge surplus for a fixed orientation implies
containment: peel to a nonempty core, then greedily embed respecting colors. -/
theorem isContained_of_coloring_cost_lt
    {A : Type u} {V : Type v} [Fintype A] [Fintype V]
    (T : SimpleGraph A) (G : SimpleGraph V)
    (cT : T.Coloring Bool) (cG : G.Coloring Bool) (hT : T.IsTree)
    (hcost : (∑ v, (Fintype.card {x : A // cT x ≠ cG v} - 1)) < G.edgeSet.ncard) :
    T.IsContained G := by
  classical
  obtain ⟨s, hs, hdegree⟩ := exists_weighted_core G
    (fun v => Fintype.card {x : A // cT x ≠ cG v} - 1) hcost
  let H := G.induce s
  let cH : H.Coloring Bool := Coloring.mk (fun x => cG x) (fun h => cG.valid h)
  have hd (v : s) : Fintype.card {x : A // cT x ≠ cH v} ≤ H.degree v := by
    have hv : Fintype.card {x : A // cT x ≠ cH v} - 1 < H.degree v := by
      simpa only [ncard_neighborSet_eq_degree] using hdegree v
    omega
  obtain ⟨v, hv⟩ := hs
  let v' : s := ⟨v, hv⟩
  have hvpos : 0 < H.degree v' := by
    have h := hdegree v'
    rw [ncard_neighborSet_eq_degree] at h
    exact lt_of_le_of_lt (Nat.zero_le _) h
  obtain ⟨w, hvw⟩ := (H.degree_pos_iff_exists_adj v').mp hvpos
  obtain ⟨f, _⟩ := exists_color_preserving_copy_of_degree T H cT cH hT
    (coloring_surjective_of_adj cH hvw) hd
  exact IsContained.trans ⟨f⟩ ⟨Copy.induce G s⟩

/-- Choose one of the two host orientations. The two total costs add to
`(k - 1) * |V|`, so positive rational edge excess makes one cost smaller than
the edge count. Positivity of both target classes justifies natural subtraction.
No ordering assumption on the two target class sizes is needed. -/
theorem exists_orientation_cost_lt {A : Type u} {V : Type v}
    [Fintype A] [Fintype V] (G : SimpleGraph V) (cT : A → Bool)
    (hsurj : Function.Surjective cT) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card A = k + 1) (hG : G.IsBipartite)
    (hedges : ((k : ℚ) - 1) / 2 * Fintype.card V < (G.edgeSet.ncard : ℚ)) :
    ∃ cG : G.Coloring Bool,
      (∑ v, (Fintype.card {x : A // cT x ≠ cG v} - 1)) < G.edgeSet.ncard := by
  classical
  obtain ⟨cG⟩ := exists_bool_coloring G hG
  let w : Bool → ℕ := fun b => Fintype.card {x : A // cT x ≠ b} - 1
  have hw (b : Bool) : w b + w (!b) = k - 1 := by
    have hsum := opposite_color_card_add cT b
    have hpos := opposite_color_card_pos cT hsurj b
    have hpos' := opposite_color_card_pos cT hsurj (!b)
    change (Fintype.card {x : A // cT x ≠ b} - 1) +
      (Fintype.card {x : A // cT x ≠ !b} - 1) = k - 1
    omega
  have hsum : (∑ v, w (cG v)) + (∑ v, w (!(cG v))) =
      (k - 1) * Fintype.card V := by
    rw [← Finset.sum_add_distrib]
    simp [hw, Nat.mul_comm]
  have hsumq : ((∑ v, w (cG v) : ℕ) : ℚ) + ((∑ v, w (!(cG v)) : ℕ) : ℚ) =
      ((k : ℚ) - 1) * Fintype.card V := by
    have h : ((∑ v, w (cG v) : ℕ) : ℚ) + ((∑ v, w (!(cG v)) : ℕ) : ℚ) =
        ((k - 1 : ℕ) : ℚ) * Fintype.card V := by exact_mod_cast hsum
    simpa only [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one] using h
  by_cases hc : (∑ v, w (cG v)) < G.edgeSet.ncard
  · exact ⟨cG, hc⟩
  · let dG : G.Coloring Bool := Coloring.mk (fun v => !(cG v))
      (fun h he => cG.valid h (Bool.not_injective he))
    refine ⟨dG, ?_⟩
    change (∑ v, w (!(cG v))) < G.edgeSet.ncard
    by_contra! hc'
    have hcq : (G.edgeSet.ncard : ℚ) ≤ ((∑ v, w (cG v) : ℕ) : ℚ) := by
      exact_mod_cast le_of_not_gt hc
    have hcq' : (G.edgeSet.ncard : ℚ) ≤ ((∑ v, w (!(cG v)) : ℕ) : ℚ) := by
      exact_mod_cast hc'
    linarith

/-- Positive rational edge excess forces a nonempty host, including at `k = 0`. -/
theorem nonempty_of_edge_threshold {V : Type v} (k : ℕ) (G : SimpleGraph V)
    (hG : ((k : ℚ) - 1) / 2 * Nat.card V < (G.edgeSet.ncard : ℚ)) :
    Nonempty V := by
  by_contra he
  letI : IsEmpty V := not_nonempty_iff.mp he
  have hbot : G = ⊥ := Subsingleton.elim _ _
  simp [hbot] at hG

/-- Elementary one-vertex embedding, also valid for an empty source.
This is copied from the leaf-induction infrastructure, with no imported helper. -/
theorem isContained_of_subsingleton {A : Type u} {V : Type v}
    [Subsingleton A] [Nonempty V] (T : SimpleGraph A) (G : SimpleGraph V) :
    T.IsContained G := by
  obtain ⟨w⟩ := ‹Nonempty V›
  refine ⟨{
    toHom := { toFun := fun _ => w, map_rel' := ?_ }
    injective' := fun _ _ _ => Subsingleton.elim _ _ }⟩
  intro x y hxy
  exact (hxy.ne (Subsingleton.elim x y)).elim

/-- **The bipartite-host Erdős–Sós theorem, with a strict rational threshold.**
For arbitrary finite vertex types, a bipartite graph with more than
`((k : ℚ) - 1) / 2 * |V|` edges contains every tree on `k + 1` vertices.

This is ordinary containment, not induced containment. The coefficient uses
rational subtraction, and the one-vertex case `k = 0` is handled separately.
No host nonemptiness or host-size hypothesis is omitted: nonemptiness follows
from the strict threshold, and the proof constructs the required injection. -/
theorem tree_isContained_of_bipartite_edge_threshold
    {A : Type u} {V : Type v} [Finite A] [Finite V]
    (T : SimpleGraph A) (G : SimpleGraph V) (k : ℕ)
    (hcard : Nat.card A = k + 1) (hT : T.IsTree) (hB : G.IsBipartite)
    (hG : ((k : ℚ) - 1) / 2 * Nat.card V < (G.edgeSet.ncard : ℚ)) :
    T.IsContained G := by
  classical
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite V
  have hcard' : Fintype.card A = k + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  by_cases hk : k = 0
  · letI : Subsingleton A := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    letI : Nonempty V := nonempty_of_edge_threshold k G hG
    exact isContained_of_subsingleton T G
  · letI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨cT⟩ := exists_bool_coloring T hT.isBipartite
    obtain ⟨cG, hcost⟩ := exists_orientation_cost_lt G cT
      (coloring_surjective_of_isTree cT hT) k (by omega) hcard' hB
      (by simpa only [Nat.card_eq_fintype_card] using hG)
    exact isContained_of_coloring_cost_lt T G cT cG hT hcost

/-- The `Fin n` host and `Fin (k + 1)` target formulation. An extra assumption
`k + 1 ≤ n` is unnecessary, since the proof already supplies an injection. -/
theorem fin_tree_isContained_of_bipartite_edge_threshold (n k : ℕ)
    (G : SimpleGraph (Fin n)) (hB : G.IsBipartite)
    (hG : ((k : ℚ) - 1) / 2 * n < (G.edgeSet.ncard : ℚ))
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree) : T.IsContained G := by
  apply tree_isContained_of_bipartite_edge_threshold T G k (by simp) hT hB
  simpa using hG

/-- The `+1` threshold used in the conjecture specification, restricted to
bipartite hosts. This does not assert the unrestricted conjecture. -/
theorem erdos_548_bipartite (n k : ℕ) (_hn : k + 1 ≤ n)
    (G : SimpleGraph (Fin n)) (hB : G.IsBipartite)
    (hG : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ))
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree) : T.IsContained G := by
  apply fin_tree_isContained_of_bipartite_edge_threshold n k G hB (by linarith) T hT

end BipartiteThreshold

/- Transitive axiom audit for every theorem and the induced-subgraph isomorphism. -/
#print axioms bool_eq_of_ne_same
#print axioms card_restrict_color_ne_le
#print axioms card_restrict_color_ne_lt
#print axioms exists_adj_fresh_of_coloring
#print axioms exists_color_preserving_copy_of_degree
#print axioms ncard_neighborSet_eq_degree
#print axioms neighborSet_ncard_iso
#print axioms edge_ncard_delete_vertex
#print axioms induceInduceIso
#print axioms exists_weighted_core
#print axioms exists_bool_coloring
#print axioms coloring_surjective_of_adj
#print axioms coloring_surjective_of_isTree
#print axioms opposite_color_card_add
#print axioms opposite_color_card_pos
#print axioms exists_color_preserving_copy_of_neighborSet_ncard
#print axioms isContained_of_coloring_cost_lt
#print axioms exists_orientation_cost_lt
#print axioms nonempty_of_edge_threshold
#print axioms isContained_of_subsingleton
#print axioms tree_isContained_of_bipartite_edge_threshold
#print axioms fin_tree_isContained_of_bipartite_edge_threshold
#print axioms erdos_548_bipartite

end Erdos548.Bipartite
